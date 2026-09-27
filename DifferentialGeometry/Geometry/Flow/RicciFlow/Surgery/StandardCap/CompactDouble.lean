import DifferentialGeometry.Topology.Manifold.StereographicCover
import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.Manifold.RadialExponential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Metric.RadialTranslation
import DifferentialGeometry.Geometry.Metric.Gluing
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff InnerProductSpace Topology Pointwise
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

def compactDoubleCapMap (north : S3) (R : ℝ) (x : E3) : S3 :=
  (stereographic' 3 north).symm ((2 * Real.exp (-R)) • radialExponentialDiffeomorph x)

def compactDoubleCapChart (north : S3) (R : ℝ) :
    E3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ stereographicImage north :=
  (radialExponentialDiffeomorph.trans
    (LinearEquiv.smulOfNeZero ℝ E3 (2 * Real.exp (-R))
      (mul_ne_zero (by norm_num) (Real.exp_ne_zero _))).toContinuousLinearEquiv.toDiffeomorph).trans
    (stereographicDiffeomorph north)

theorem compactDoubleCapChart_coe (north : S3) (R : ℝ) (x : E3) :
    (compactDoubleCapChart north R x : S3) = compactDoubleCapMap north R x := rfl

private def chartMetric (north : S3) (R : ℝ) :
    SmoothRiemannianMetric (𝓡 3) (stereographicImage north) :=
  Diffeomorph.pullbackMetricCross metric (compactDoubleCapChart north R).symm

private theorem chartMetric_pullback (north : S3) (R : ℝ) (x v w : E3) :
    (chartMetric north R).inner (compactDoubleCapChart north R x)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapChart north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapChart north R) x w) = metric.inner x v w := by
  let D := compactDoubleCapChart north R
  have he : (D.symm : stereographicImage north → E3) ∘ D = id := funext D.symm_apply_apply
  have hd := mfderiv_comp x (D.symm.contMDiff.mdifferentiable (by simp) (D x))
    (D.contMDiff.mdifferentiable (by simp) x)
  rw [he, mfderiv_id] at hd
  have hv := congrArg (fun A => A v) hd.symm
  have hw := congrArg (fun A => A w) hd.symm
  change metric.inner (D.symm (D x))
    (mfderiv (𝓡 3) (𝓡 3) D.symm (D x) (mfderiv (𝓡 3) (𝓡 3) D x v))
    (mfderiv (𝓡 3) (𝓡 3) D.symm (D x) (mfderiv (𝓡 3) (𝓡 3) D x w)) = _
  dsimp only [TangentSpace] at hv hw ⊢
  erw [hv, hw, D.symm_apply_apply]
  rfl

private def leftOpen (north : S3) : TopologicalSpace.Opens S3 :=
  stereographicBallImage (n := 3) north (2 * Real.exp 1)

private def rightOpen (north : S3) : TopologicalSpace.Opens S3 :=
  ⟨(sphereAntipodalDiffeomorph (n := 3)) ⁻¹' (leftOpen north : Set S3),
    (leftOpen north).isOpen.preimage (sphereAntipodalDiffeomorph (n := 3)).contMDiff.continuous⟩

private theorem left_subset (north : S3) : leftOpen north ≤ stereographicImage north := by
  intro p hp
  change p ∈ (stereographicImage north : Set S3)
  rw [stereographicImage_eq]
  exact stereographicBallImage_subset_punctured (n := 3) north (2 * Real.exp 1) hp

private theorem open_cover (north : S3) (p : S3) : p ∈ leftOpen north ∨ p ∈ rightOpen north := by
  apply stereographicBallImage_antipodal_cover (n := 3) north (2 * Real.exp 1) _ p
  have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  linarith

private def antipodalBetween (north : S3) :
    rightOpen north ≃ₘ⟮𝓡 3, 𝓡 3⟯ leftOpen north where
  toFun := fun p => ⟨sphereAntipodalDiffeomorph (n := 3) p.val, p.property⟩
  invFun := fun p => ⟨sphereAntipodalDiffeomorph (n := 3) p.val, by
    change -(-p.val) ∈ leftOpen north
    simpa only [neg_neg] using p.property⟩
  left_inv := by intro p; apply Subtype.ext; exact neg_neg p.val
  right_inv := by intro p; apply Subtype.ext; exact neg_neg p.val
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (leftOpen north) _).mp
    exact (sphereAntipodalDiffeomorph (n := 3)).contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (rightOpen north) _).mp
    exact (sphereAntipodalDiffeomorph (n := 3)).contMDiff.comp contMDiff_subtype_val

private def leftMetric (north : S3) (R : ℝ) : SmoothRiemannianMetric (𝓡 3) (leftOpen north) :=
  (chartMetric north R).restrictOpenOfSubset (left_subset north)

private def rightMetric (north : S3) (R : ℝ) : SmoothRiemannianMetric (𝓡 3) (rightOpen north) :=
  Diffeomorph.pullbackMetricCross (leftMetric north R) (antipodalBetween north)

private theorem cap_antipodal_overlap (north : S3) (R : ℝ) (x : E3)
    (hx : max transitionEnd 2 ≤ ‖x‖) (hy : max transitionEnd 2 ≤ 2 * R - ‖x‖) :
    let F := fun y : E3 => (stereographic' 3 north).symm
      ((2 * Real.exp (-R)) • radialExponentialDiffeomorph y)
    sphereAntipodalDiffeomorph (n := 3) (F x) = F (radialTranslation (-2 * R) x) ∧
      ∀ v w : E3,
        metric.inner (radialTranslation (-2 * R) x)
          (mfderiv (𝓡 3) (𝓡 3) (radialTranslation (-2 * R)) x v)
          (mfderiv (𝓡 3) (𝓡 3) (radialTranslation (-2 * R)) x w) = metric.inner x v w := by
  let y := radialTranslation (-2 * R) x
  have hr : 0 < ‖x‖ := transitionEnd_pos.trans_le ((le_max_left _ _).trans hx)
  have hρ : 0 < 2 * R - ‖x‖ := transitionEnd_pos.trans_le ((le_max_left _ _).trans hy)
  have hx0 : x ≠ 0 := norm_pos_iff.mp hr
  have hn : ‖y‖ = 2 * R - ‖x‖ := by
    dsimp only [y]
    rw [radialTranslation, norm_smul, Real.norm_eq_abs,
      abs_of_neg (div_neg_of_neg_of_pos (by linarith) hr)]
    field_simp
    ring
  constructor
  · let z := (2 * Real.exp (-R)) • radialExponentialDiffeomorph x
    have hz : z ≠ 0 := by
      apply smul_ne_zero (mul_ne_zero (by norm_num) (Real.exp_ne_zero _))
      have hh := norm_radialExponentialDiffeomorph x ((le_max_right _ _).trans hx)
      exact norm_pos_iff.mp (hh.trans_gt (Real.exp_pos _))
    have hnormz : ‖z‖ = 2 * Real.exp (-R) * Real.exp ‖x‖ := by
      dsimp only [z]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (mul_pos (by norm_num) (Real.exp_pos _)),
        norm_radialExponentialDiffeomorph x ((le_max_right _ _).trans hx)]
    have he : ((-4 / ‖z‖ ^ 2) • z) =
        (2 * Real.exp (-R)) • radialExponentialDiffeomorph y := by
      rw [hnormz]
      dsimp only [z]
      rw [radialExponentialDiffeomorph_of_two_le_norm x ((le_max_right _ _).trans hx),
        radialExponentialDiffeomorph_of_two_le_norm y (by rw [hn]; exact (le_max_right _ _).trans hy), hn]
      simp only [y, radialTranslation, smul_smul]
      congr 1
      have htwice : Real.exp (2 * R) = Real.exp R ^ 2 := by
        rw [two_mul, Real.exp_add, pow_two]
      rw [Real.exp_neg, Real.exp_sub, htwice]
      field_simp [hρ.ne', hr.ne']
      ring
    change -(stereographic' 3 north).symm z = (stereographic' 3 north).symm _
    rw [← stereographicInverse_antipodal north z hz, he]
  · intro v w
    rw [mfderiv_eq_fderiv]
    calc
      _ = radialBilinearField (fun _ => Real.sqrt 2) y
          (fderiv ℝ (radialTranslation (-2 * R)) x v)
          (fderiv ℝ (radialTranslation (-2 * R)) x w) :=
        metric_inner_cylindrical (by rw [hn]; exact (le_max_left _ _).trans hy) _ _
      _ = radialBilinearField (fun _ => Real.sqrt 2) x v w := by
        rw [fderiv_radialTranslation_apply _ hx0, fderiv_radialTranslation_apply _ hx0]
        simp only [radialBilinearField_apply, hn]
        simp only [y, radialTranslation, inner_sub_left, inner_sub_right, real_inner_smul_left,
          real_inner_smul_right, real_inner_comm v x, real_inner_comm w x,
          real_inner_self_eq_norm_sq]
        field_simp
        ring
      _ = _ := (metric_inner_cylindrical ((le_max_left _ _).trans hx) v w).symm

private theorem cap_mem_left (north : S3) (R : ℝ) (hR : 2 ≤ R + 1) (x : E3) :
    compactDoubleCapMap north R x ∈ leftOpen north ↔ ‖x‖ < R + 1 := by
  change (stereographic' 3 north).symm _ ∈ stereographicBallImage (n := 3) north _ ↔ _
  rw [mem_stereographicBallImage_inverse, norm_smul, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) (Real.exp_pos _))]
  have he : 2 * Real.exp 1 = (2 * Real.exp (-R)) * Real.exp (R + 1) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, mul_lt_mul_iff_right₀ (mul_pos (by norm_num) (Real.exp_pos _))]
  exact norm_radialExponentialDiffeomorph_lt_iff x (R + 1) hR

private theorem overlap_radii (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (x : E3)
    (hxL : compactDoubleCapMap north R x ∈ leftOpen north)
    (hxR : compactDoubleCapMap north R x ∈ rightOpen north) :
    max transitionEnd 2 < ‖x‖ ∧ max transitionEnd 2 < 2 * R - ‖x‖ := by
  have hm : 2 ≤ max transitionEnd 2 := le_max_right _ _
  have hu : ‖x‖ < R + 1 := (cap_mem_left north R (by linarith) x).mp hxL
  let z := (2 * Real.exp (-R)) • radialExponentialDiffeomorph x
  have hz : z ≠ 0 := by
    intro hz
    have hzero : (stereographic' 3 north).symm (0 : E3) = -north := by
      apply Subtype.ext
      change ((stereographic' 3 north).symm 0 : E4) = -(north : E4)
      norm_num [stereographic'_symm_apply, smul_smul]
    have hp : compactDoubleCapMap north R x = -north := by
      change (stereographic' 3 north).symm z = -north
      rw [hz, hzero]
    change -(compactDoubleCapMap north R x) ∈ leftOpen north at hxR
    rw [hp, neg_neg] at hxR
    have hh := stereographicBallImage_subset_punctured (n := 3) north (2 * Real.exp 1) hxR
    exact hh (by simp)
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hi : 4 / ‖z‖ < 2 * Real.exp 1 := by
    have hh : (stereographic' 3 north).symm ((-4 / ‖z‖ ^ 2) • z) ∈ leftOpen north := by
      rw [stereographicInverse_antipodal north z hz]
      exact hxR
    have hh' := (mem_stereographicBallImage_inverse north (2 * Real.exp 1) _).mp hh
    have hn : ‖(-4 / ‖z‖ ^ 2) • z‖ = 4 / ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_neg (div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hzpos))]
      field_simp
    simpa only [hn] using hh'
  have hl : R - 1 ≤ ‖x‖ := by
    by_contra! hh
    have he := (norm_radialExponentialDiffeomorph_lt_iff x (R - 1) (by linarith)).mpr hh
    have hn : ‖z‖ < 2 * Real.exp (-1) := by
      have hnz : ‖z‖ = (2 * Real.exp (-R)) * ‖radialExponentialDiffeomorph x‖ := by
        dsimp only [z]
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (mul_pos (by norm_num) (Real.exp_pos _))]
      rw [hnz]
      have heq : 2 * Real.exp (-1) = (2 * Real.exp (-R)) * Real.exp (R - 1) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      rw [heq]
      exact mul_lt_mul_of_pos_left he (mul_pos (by norm_num) (Real.exp_pos _))
    have hproduct : (2 * Real.exp 1) * (2 * Real.exp (-1)) = 4 := by
      rw [Real.exp_neg]
      field_simp
      ring
    have hbound := mul_lt_mul_of_pos_left hn (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos 1))
    rw [hproduct] at hbound
    have hbad := (div_lt_iff₀ hzpos).mp hi
    linarith
  constructor <;> linarith

theorem contMDiff_compactDoubleCapMap (north : S3) (R : ℝ) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (compactDoubleCapMap north R) :=
  contMDiff_subtype_val.comp (compactDoubleCapChart north R).contMDiff

private theorem compactDoubleCapChart_mfderiv (north : S3) (R : ℝ) (x : E3) :
    mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapChart north R) x =
      mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x := by
  have he : (Subtype.val : stereographicImage north → S3) ∘ compactDoubleCapChart north R =
      compactDoubleCapMap north R := rfl
  rw [← he, mfderiv_comp x (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((compactDoubleCapChart north R).contMDiff.mdifferentiableAt (by simp)), mfderiv_subtype_val]
  rfl

private theorem antipodalBetween_mfderiv (north : S3) (p : rightOpen north) :
    mfderiv (𝓡 3) (𝓡 3) (antipodalBetween north) p =
      mfderiv (𝓡 3) (𝓡 3) (sphereAntipodalDiffeomorph (n := 3)) p.val := by
  have he : (Subtype.val : leftOpen north → S3) ∘ antipodalBetween north =
      (sphereAntipodalDiffeomorph (n := 3) : S3 → S3) ∘ Subtype.val := rfl
  have hh := mfderiv_congr (I := 𝓡 3) (I' := 𝓡 3) (x := p) he
  rw [mfderiv_comp p (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
      ((antipodalBetween north).contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp p ((sphereAntipodalDiffeomorph (n := 3)).contMDiff.mdifferentiableAt (by simp))
      (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)), mfderiv_subtype_val,
    mfderiv_subtype_val] at hh
  exact hh

private theorem overlap_differential (north : S3) (R : ℝ) (x : E3)
    (hx : max transitionEnd 2 < ‖x‖) (hy : max transitionEnd 2 < 2 * R - ‖x‖) :
    (mfderiv (𝓡 3) (𝓡 3) (sphereAntipodalDiffeomorph (n := 3))
      (compactDoubleCapMap north R x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x) =
    (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) (radialTranslation (-2 * R) x)).comp
      (mfderiv (𝓡 3) (𝓡 3) (radialTranslation (-2 * R)) x) := by
  have he : ((sphereAntipodalDiffeomorph (n := 3) : S3 → S3) ∘ compactDoubleCapMap north R)
      =ᶠ[𝓝 x] (compactDoubleCapMap north R ∘ radialTranslation (-2 * R)) := by
    have hO : IsOpen {y : E3 | max transitionEnd 2 < ‖y‖ ∧
        max transitionEnd 2 < 2 * R - ‖y‖} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_const (continuous_const.sub continuous_norm))
    filter_upwards [hO.mem_nhds ⟨hx, hy⟩] with y h
    exact (cap_antipodal_overlap north R y h.1.le h.2.le).1
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith [le_max_right transitionEnd 2])
  have hh := he.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x ((sphereAntipodalDiffeomorph (n := 3)).contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_compactDoubleCapMap north R).mdifferentiableAt (by simp)),
    mfderiv_comp x ((contMDiff_compactDoubleCapMap north R).mdifferentiableAt (by simp))
      ((contDiffAt_radialTranslation (-2 * R) hx0).contMDiffAt.mdifferentiableAt (by simp))] at hh
  exact hh

private theorem leftMetric_pullback (north : S3) (R : ℝ) (x : E3)
    (hx : compactDoubleCapMap north R x ∈ leftOpen north) (v w : E3) :
    (leftMetric north R).inner ⟨compactDoubleCapMap north R x, hx⟩
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) = metric.inner x v w := by
  change (chartMetric north R).inner (compactDoubleCapChart north R x) _ _ = _
  have hh := chartMetric_pullback north R x v w
  erw [compactDoubleCapChart_mfderiv] at hh
  exact hh

private theorem rightMetric_pullback_on_overlap (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (x : E3)
    (hxL : compactDoubleCapMap north R x ∈ leftOpen north)
    (hxR : compactDoubleCapMap north R x ∈ rightOpen north) (v w : E3) :
    (rightMetric north R).inner ⟨compactDoubleCapMap north R x, hxR⟩
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) = metric.inner x v w := by
  obtain ⟨hx, hy⟩ := overlap_radii north R hR x hxL hxR
  let y := radialTranslation (-2 * R) x
  have hpoint : sphereAntipodalDiffeomorph (n := 3) (compactDoubleCapMap north R x) =
      compactDoubleCapMap north R y := (cap_antipodal_overlap north R x hx.le hy.le).1
  have hbase : TopologicalSpace.Opens.inclusion (left_subset north)
      (antipodalBetween north ⟨compactDoubleCapMap north R x, hxR⟩) = compactDoubleCapChart north R y :=
    Subtype.ext hpoint
  have hd := overlap_differential north R x hx hy
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  change (chartMetric north R).inner
    (TopologicalSpace.Opens.inclusion (left_subset north)
      (antipodalBetween north ⟨compactDoubleCapMap north R x, hxR⟩))
    (mfderiv (𝓡 3) (𝓡 3) (antipodalBetween north) ⟨compactDoubleCapMap north R x, hxR⟩
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v))
    (mfderiv (𝓡 3) (𝓡 3) (antipodalBetween north) ⟨compactDoubleCapMap north R x, hxR⟩
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w)) = _
  dsimp only [TangentSpace] at hv hw ⊢
  erw [hbase, antipodalBetween_mfderiv, hv, hw, ← compactDoubleCapChart_mfderiv]
  exact (chartMetric_pullback north R y _ _).trans
    ((cap_antipodal_overlap north R x hx.le hy.le).2 v w)

private theorem metric_overlap (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R)
    (p : S3) (hpL : p ∈ leftOpen north) (hpR : p ∈ rightOpen north)
    (v w : TangentSpace (𝓡 3) p) :
    (leftMetric north R).inner ⟨p, hpL⟩ v w = (rightMetric north R).inner ⟨p, hpR⟩ v w := by
  obtain ⟨x, hx⟩ := (compactDoubleCapChart north R).surjective ⟨p, left_subset north hpL⟩
  have hp : compactDoubleCapMap north R x = p := congrArg Subtype.val hx
  subst p
  obtain ⟨a, ha⟩ := ((compactDoubleCapChart north R).mfderivToContinuousLinearEquiv (by simp) x).surjective v
  obtain ⟨b, hb⟩ := ((compactDoubleCapChart north R).mfderivToContinuousLinearEquiv (by simp) x).surjective w
  change mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapChart north R) x a = v at ha
  change mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapChart north R) x b = w at hb
  erw [compactDoubleCapChart_mfderiv] at ha hb
  dsimp only [TangentSpace] at ha hb ⊢
  erw [← ha, ← hb]
  exact (leftMetric_pullback north R x hpL a b).trans
    (rightMetric_pullback_on_overlap north R hR x hpL hpR a b).symm

private def wholeUnionChart (north : S3) :
    S3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ ↥(leftOpen north ⊔ rightOpen north) where
  toFun := fun p => ⟨p, open_cover north p⟩
  invFun := Subtype.val
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (leftOpen north ⊔ rightOpen north) _).mp
    exact contMDiff_id
  contMDiff_invFun := contMDiff_subtype_val

private theorem wholeUnionChart_mfderiv (north : S3) (p : S3) :
    mfderiv (𝓡 3) (𝓡 3) (wholeUnionChart north) p = ContinuousLinearMap.id ℝ E3 := by
  have he : (Subtype.val : ↥(leftOpen north ⊔ rightOpen north) → S3) ∘
      wholeUnionChart north = id := rfl
  have hh := mfderiv_congr (I := 𝓡 3) (I' := 𝓡 3) (x := p) he
  rw [mfderiv_comp p (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((wholeUnionChart north).contMDiff.mdifferentiableAt (by simp)), mfderiv_subtype_val,
    mfderiv_id] at hh
  exact hh

def compactDoubleMetric (north : S3) (R : ℝ) (hR : max transitionEnd 2 + 2 ≤ R) :
    SmoothRiemannianMetric (𝓡 3) S3 :=
  Diffeomorph.pullbackMetricCross
    (DifferentialGeometry.Geometry.Metric.glueMetric (leftOpen north) (rightOpen north)
      (leftMetric north R) (rightMetric north R) (metric_overlap north R hR))
    (wholeUnionChart north)

private theorem compactDoubleMetric_left (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (p : S3) (hp : p ∈ leftOpen north)
    (v w : TangentSpace (𝓡 3) p) :
    (compactDoubleMetric north R hR).inner p v w = (leftMetric north R).inner ⟨p, hp⟩ v w := by
  unfold compactDoubleMetric
  rw [Diffeomorph.pullbackMetricCross_inner, wholeUnionChart_mfderiv]
  exact DifferentialGeometry.Geometry.Metric.glueMetric_inner_left (leftOpen north) (rightOpen north)
    (leftMetric north R) (rightMetric north R) (metric_overlap north R hR) ⟨p, hp⟩ v w

private theorem compactDoubleMetric_right (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (p : S3) (hp : p ∈ rightOpen north)
    (v w : TangentSpace (𝓡 3) p) :
    (compactDoubleMetric north R hR).inner p v w = (rightMetric north R).inner ⟨p, hp⟩ v w := by
  unfold compactDoubleMetric
  rw [Diffeomorph.pullbackMetricCross_inner, wholeUnionChart_mfderiv]
  exact DifferentialGeometry.Geometry.Metric.glueMetric_inner_right (leftOpen north) (rightOpen north)
    (leftMetric north R) (rightMetric north R) (metric_overlap north R hR) ⟨p, hp⟩ v w

theorem compactDoubleMetric_cap_pullback (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) (v w : E3) :
    (compactDoubleMetric north R hR).inner (compactDoubleCapMap north R x)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) = metric.inner x v w := by
  have hp := (cap_mem_left north R (by linarith [le_max_right transitionEnd 2]) x).mpr
    (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  exact (compactDoubleMetric_left north R hR _ hp _ _).trans (leftMetric_pullback north R x hp v w)

theorem compactDoubleMetric_antipodal_cap_pullback (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) (v w : E3) :
    let F := (sphereAntipodalDiffeomorph (n := 3) : S3 → S3) ∘ compactDoubleCapMap north R
    (compactDoubleMetric north R hR).inner (F x)
      (mfderiv (𝓡 3) (𝓡 3) F x v) (mfderiv (𝓡 3) (𝓡 3) F x w) = metric.inner x v w := by
  intro F
  have hp := (cap_mem_left north R (by linarith [le_max_right transitionEnd 2]) x).mpr
    (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have hq : F x ∈ rightOpen north := by
    change -(-(compactDoubleCapMap north R x)) ∈ leftOpen north
    simpa only [neg_neg] using hp
  have he : (sphereAntipodalDiffeomorph (n := 3) : S3 → S3) ∘ F = compactDoubleCapMap north R := by
    funext y
    exact neg_neg _
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F :=
    (sphereAntipodalDiffeomorph (n := 3)).contMDiff.comp (contMDiff_compactDoubleCapMap north R)
  have hd := mfderiv_comp x ((sphereAntipodalDiffeomorph (n := 3)).contMDiff.mdifferentiableAt (by simp))
    (hF.mdifferentiableAt (by simp))
  rw [he] at hd
  have hv := congrArg (fun A => A v) hd.symm
  have hw := congrArg (fun A => A w) hd.symm
  have hbase : antipodalBetween north ⟨F x, hq⟩ = ⟨compactDoubleCapMap north R x, hp⟩ :=
    Subtype.ext (neg_neg _)
  calc
    _ = (rightMetric north R).inner ⟨F x, hq⟩
        (mfderiv (𝓡 3) (𝓡 3) F x v) (mfderiv (𝓡 3) (𝓡 3) F x w) :=
      compactDoubleMetric_right north R hR _ hq _ _
    _ = (leftMetric north R).inner ⟨compactDoubleCapMap north R x, hp⟩
        (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
        (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) := by
      change (leftMetric north R).inner (antipodalBetween north ⟨F x, hq⟩)
        (mfderiv (𝓡 3) (𝓡 3) (antipodalBetween north) ⟨F x, hq⟩ (mfderiv (𝓡 3) (𝓡 3) F x v))
        (mfderiv (𝓡 3) (𝓡 3) (antipodalBetween north) ⟨F x, hq⟩ (mfderiv (𝓡 3) (𝓡 3) F x w)) = _
      dsimp only [TangentSpace] at hv hw ⊢
      erw [hbase, antipodalBetween_mfderiv, hv, hw]
    _ = _ := leftMetric_pullback north R x hp v w

private theorem cap_ball_image (north : S3) (R : ℝ) :
    let F := fun x : E3 => (stereographic' 3 north).symm
      ((2 * Real.exp (-R)) • radialExponentialDiffeomorph x)
    ∀ b : ℝ, 2 ≤ R + b → F '' Metric.ball 0 (R + b) =
      (stereographic' 3 north).symm '' Metric.ball 0 (2 * Real.exp b) := by
  intro F b hb
  have hs : 2 * Real.exp (-R) ≠ 0 := mul_ne_zero (by norm_num) (Real.exp_ne_zero _)
  have he : ‖2 * Real.exp (-R)‖ * Real.exp (R + b) = 2 * Real.exp b := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) (Real.exp_pos _)),
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc
    _ = (stereographic' 3 north).symm ''
        ((fun y : E3 => (2 * Real.exp (-R)) • y) ''
          (radialExponentialDiffeomorph '' Metric.ball (0 : E3) (R + b))) := by
      rw [image_image, image_image]
    _ = (stereographic' 3 north).symm ''
        ((2 * Real.exp (-R)) • Metric.ball (0 : E3) (Real.exp (R + b))) := by
      rw [radialExponentialDiffeomorph_image_ball (R + b) hb]
      rfl
    _ = _ := by rw [_root_.smul_ball hs, smul_zero, he]

theorem compactDoubleCapMap_cover (north : S3) (R : ℝ) (hR : 2 ≤ R + 1) :
    ∀ p : S3, ∃ x ∈ Metric.ball (0 : E3) (R + 1),
      compactDoubleCapMap north R x = p ∨
        sphereAntipodalDiffeomorph (n := 3) (compactDoubleCapMap north R x) = p := by
  let F := compactDoubleCapMap north R
  intro p
  have hr : 2 < 2 * Real.exp 1 := by
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have himage : F '' Metric.ball 0 (R + 1) =
      (stereographicBallImage (n := 3) north (2 * Real.exp 1) : Set S3) :=
    cap_ball_image north R 1 hR
  have hpreimage (q : S3)
      (hq : q ∈ stereographicBallImage (n := 3) north (2 * Real.exp 1)) :
      ∃ x ∈ Metric.ball (0 : E3) (R + 1), F x = q := by
    change q ∈ F '' Metric.ball (0 : E3) (R + 1)
    rw [himage]
    exact hq
  rcases stereographicBallImage_antipodal_cover (n := 3) north (2 * Real.exp 1) hr p with hp | hp
  · obtain ⟨x, hx, he⟩ := hpreimage _ hp
    exact ⟨x, hx, Or.inl he⟩
  · obtain ⟨x, hx, he⟩ := hpreimage _ hp
    refine ⟨x, hx, Or.inr ?_⟩
    have ha := congrArg (sphereAntipodalDiffeomorph (n := 3) : S3 → S3) he
    change -(F x) = -(-p) at ha
    change -(F x) = p
    simpa only [neg_neg] using ha
end DifferentialGeometry.PDE.RicciFlow.StandardCap
