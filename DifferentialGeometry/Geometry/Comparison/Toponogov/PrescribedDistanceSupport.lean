import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


theorem curveVelocity_affine
    (γ : ℝ → M) (c d t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d)) :
    curveVelocity (I := I) (fun s => γ (c * s + d)) t =
      c • curveVelocity (I := I) γ (c * t + d) := by
  let a : ℝ → ℝ := fun s => c * s + d
  have ha : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t := by
    have ha_inf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ a := by
      exact contMDiff_const.mul contMDiff_id |>.add contMDiff_const
    exact ha_inf.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp :=
    mfderiv_comp_apply (f := a) (g := γ) (x := t) hγ ha (1 : ℝ)
  have ha_one : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t (1 : ℝ) = c := by
    rw [mfderiv_eq_fderiv]
    have hfd : HasFDerivAt a (c • (1 : ℝ →L[ℝ] ℝ)) t := by
      let : NormedAddCommGroup ℝ := Real.normedAddCommGroup
      let : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
      change HasFDerivAt (fun s : ℝ => c * s + d) (c • (1 : ℝ →L[ℝ] ℝ)) t
      exact ((hasFDerivAt_id t).const_mul c).add_const d
    rw [hfd.fderiv]
    change c • ((1 : ℝ →L[ℝ] ℝ) (1 : ℝ)) = c
    rw [one_apply_eq_self, smul_eq_mul, mul_one]
  change mfderiv 𝓘(ℝ, ℝ) I (γ ∘ a) t (1 : ℝ) =
    c • mfderiv 𝓘(ℝ, ℝ) I γ (a t) (1 : ℝ)
  rw [hcomp, ha_one]
  change mfderiv 𝓘(ℝ, ℝ) I γ (a t) c =
    c • mfderiv 𝓘(ℝ, ℝ) I γ (a t) (1 : ℝ)
  calc
    mfderiv 𝓘(ℝ, ℝ) I γ (a t) c =
        mfderiv 𝓘(ℝ, ℝ) I γ (a t) (c • (1 : ℝ)) := by
      rw [smul_eq_mul, mul_one]
    _ = c • mfderiv 𝓘(ℝ, ℝ) I γ (a t) (1 : ℝ) :=
      map_smul (mfderiv 𝓘(ℝ, ℝ) I γ (a t)) c (1 : ℝ)

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem prescribed_tail_curve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) (s : ℝ) :
    let z := intrinsicVelocityLift (I := I) g hEnorm p v s
    intrinsicGeodesic (I := I) g hEnorm z.proj ((1 - s) • z.snd) =
      fun t => intrinsicGeodesic (I := I) g hEnorm p v ((1 - s) * t + s) := by
  dsimp only
  funext t
  calc
    _ = intrinsicGeodesic (I := I) g hEnorm
        (intrinsicVelocityLift (I := I) g hEnorm p v s).proj
        (intrinsicVelocityLift (I := I) g hEnorm p v s).snd ((1 - s) * t) :=
      intrinsicGeo_smul_apply (I := I) g hEnorm
        (intrinsicVelocityLift (I := I) g hEnorm p v s).proj
        (intrinsicVelocityLift (I := I) g hEnorm p v s).snd (1 - s) t
    _ = _ := (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm p v s)
      ((1 - s) * t)).symm

private theorem prescribed_tail_velocity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) (s : ℝ) :
    let z := intrinsicVelocityLift (I := I) g hEnorm p v s
    ((intrinsicVelocityLift (I := I) g hEnorm z.proj ((1 - s) • z.snd) 1).snd : E) =
      (1 - s) • ((intrinsicVelocityLift (I := I) g hEnorm p v 1).snd : E) := by
  dsimp only
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v
  let eta : ℝ → M := intrinsicGeodesic (I := I) g hEnorm
    (intrinsicVelocityLift (I := I) g hEnorm p v s).proj
    ((1 - s) • (intrinsicVelocityLift (I := I) g hEnorm p v s).snd)
  have heta : eta = fun t => gamma ((1 - s) * t + s) :=
    prescribed_tail_curve (I := I) g hEnorm p v s
  have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma ((1 - s) * 1 + s) :=
    (intrinsicGeodesic_contMDiff (I := I) g hEnorm p v).contMDiffAt.mdifferentiableAt
      (by simp)
  have hvel := curveVelocity_affine (I := I) gamma (1 - s) s 1 hdiff
  have htime : (1 - s) * 1 + s = 1 := by ring
  rw [htime] at hvel
  change (curveVelocity (I := I) eta 1 : E) =
    (1 - s) • (curveVelocity (I := I) gamma 1 : E)
  rw [heta]
  exact hvel

theorem smooth_distance_upper_support_of_minimizing_exp
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) (hv : 0 < g.inner p v v)
    (hmin : Real.sqrt (g.inner p v v) =
      (riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p v 1)).toReal) :
    let x := intrinsicGeodesic (I := I) g hEnorm p v 1
    ∃ rho : M → ℝ, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ rho x ∧
      rho x = Real.sqrt (g.inner p v v) ∧
      (∀ᶠ y in 𝓝 x, (riemannianEDist I p y).toReal ≤ rho y) ∧
      gradientFun (I := I) g rho x = (Real.sqrt (g.inner p v v))⁻¹ •
        curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p v) 1 := by
  dsimp only
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v
  let x : M := gamma 1
  let r : ℝ := Real.sqrt (g.inner p v v)
  have hr : 0 < r := Real.sqrt_pos.mpr hv
  have hexp : expMapIntrinsic (I := I) g hEnorm p v = x := rfl
  have hr_def : r = (riemannianEDist I p x).toReal := hmin
  have hfin : riemannianEDist I p x ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hr_def
    linarith
  let s : ℝ := 1 / 2
  have hs : s ∈ Ioo (0 : ℝ) 1 := by norm_num [s]
  let z := intrinsicVelocityLift (I := I) g hEnorm p v s
  let u : TangentSpace I z.proj := (1 - s) • z.snd
  have hnot : ¬ IsConjVec (I := I) g hEnorm z.proj
      (tangentSpaceModelContinuousLinearEquiv (I := I) z.proj u) := by
    with_unfolding_all
      exact tail_not_conj_of_min (I := I) g hEnorm v hexp hmin (hr_def ▸ hr) hs
  obtain ⟨B, hsource⟩ := branch_of_not_conj (I := I) g hEnorm hnot
  have htail : intrinsicGeodesic (I := I) g hEnorm z.proj u =
      fun t => gamma ((1 - s) * t + s) :=
    prescribed_tail_curve (I := I) g hEnorm p v s
  have hexp_tail : expMapIntrinsic (I := I) g hEnorm z.proj u = x := by
    change intrinsicGeodesic (I := I) g hEnorm z.proj u 1 = x
    rw [htail]
    change gamma ((1 - s) * 1 + s) = x
    have htime : (1 - s) * 1 + s = 1 := by ring
    rw [htime]
  have hspeed : g.inner z.proj z.snd z.snd = g.inner p v v := by
    with_unfolding_all exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v s
  have hunorm : Real.sqrt (g.inner z.proj u u) = (1 - s) * r := by
    dsimp only [u]
    rw [sqrt_gInner_smul_self (I := I) g z.proj (sub_nonneg.mpr hs.2.le), hspeed]
  have hu_pos : 0 < g.inner z.proj u u :=
    Real.sqrt_pos.mp (hunorm.symm ▸ mul_pos (sub_pos.mpr hs.2) hr)
  have hleft : riemannianEDist I p z.proj = ENNReal.ofReal (s * r) := by
    change riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p v s) = ENNReal.ofReal (s * r)
    exact minSegment_edist (I := I) g hEnorm v hexp rfl hr_def hfin
      ⟨hs.1.le, hs.2.le⟩
  have hmap : B.hom (tangentSpaceModelContinuousLinearEquiv (I := I) z.proj u) = x :=
    (B.hom_eq hsource).symm.trans hexp_tail
  have hxB : x ∈ B.hom.target := by
    rw [← hmap]
    exact B.hom.map_source hsource
  have hbr : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (branchRadius (I := I) g B) x := by
    have h := branchRadius_infAt (I := I) B hsource hu_pos
    rwa [hexp_tail] at h
  let rho : M → ℝ := fun y => s * r + branchRadius (I := I) g B y
  have hrho : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ rho x := contMDiffAt_const.add hbr
  have hrad : branchRadius (I := I) g B x = (1 - s) * r := by
    rw [← hexp_tail, branchRadius_exp (I := I) B hsource]
    exact hunorm
  have hvalue : rho x = r := by
    dsimp only [rho]
    rw [hrad]
    ring
  have hupper : ∀ᶠ y in 𝓝 x, (riemannianEDist I p y).toReal ≤ rho y := by
    filter_upwards [B.hom.open_target.mem_nhds hxB] with y hy
    have hdist : riemannianEDist I p y ≤
        ENNReal.ofReal (s * r) + ENNReal.ofReal (branchRadius (I := I) g B y) := by
      calc
        _ ≤ riemannianEDist I p z.proj + riemannianEDist I z.proj y :=
          riemannianEDist_triangle
        _ ≤ _ := add_le_add hleft.le (B.edist_le_radius hy)
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hdist
    have hrad_nonneg : 0 ≤ branchRadius (I := I) g B y := Real.sqrt_nonneg _
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (mul_nonneg hs.1.le hr.le),
      ENNReal.toReal_ofReal hrad_nonneg] at hreal
  have hgrad_rho : gradientFun (I := I) g rho x =
      gradientFun (I := I) g (branchRadius (I := I) g B) x := by
    dsimp only [rho]
    rw [gradientFun_add (I := I) g mdifferentiableAt_const
      (hbr.mdifferentiableAt (by simp)), gradientFun_const, zero_add]
  have hgrad_br : gradientFun (I := I) g (branchRadius (I := I) g B) x =
      ((1 - s) * r)⁻¹ • ((1 - s) • curveVelocity (I := I) gamma 1) := by
    have h := grad_branchRadius (I := I) B hsource hu_pos
    rw [hexp_tail, hunorm] at h
    have hvel := prescribed_tail_velocity (I := I) g hEnorm p v s
    change (gradientFun (I := I) g (branchRadius (I := I) g B) x : E) = _ at h ⊢
    change ((intrinsicVelocityLift (I := I) g hEnorm z.proj u 1).snd : E) =
      (1 - s) • (curveVelocity (I := I) gamma 1 : E) at hvel
    rw [hvel] at h
    exact h
  refine ⟨rho, hrho, hvalue, hupper, ?_⟩
  rw [hgrad_rho, hgrad_br, smul_smul]
  have hcoeff : ((1 - s) * r)⁻¹ * (1 - s) = r⁻¹ := by
    field_simp [hr.ne', (sub_pos.mpr hs.2).ne']
  rw [hcoeff]

end DifferentialGeometry.Geometry.Comparison.Toponogov

end
