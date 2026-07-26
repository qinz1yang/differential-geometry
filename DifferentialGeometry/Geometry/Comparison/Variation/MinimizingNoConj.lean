import DifferentialGeometry.Geometry.Comparison.HalfSqDistGrad
import DifferentialGeometry.Geometry.Comparison.Variation.MinimalGeodesicNoConjugate
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity

set_option autoImplicit false

/-!
# Nonconjugacy along a shifted minimizing tail

This module transports the interior no-conjugate theorem to a fixed early point
of a minimizing intrinsic geodesic.  The endpoint case is obtained by reversing
the tail; the closed-tail statement combines it with ordinary interior
nonconjugacy.
-/

open Set Function Manifold Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)] in
private theorem curveVel_affine
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
      simpa only [a] using
        (((hasFDerivAt_id t).const_mul c).add_const d)
    rw [hfd.fderiv]
    change c • ((1 : ℝ →L[ℝ] ℝ) (1 : ℝ)) = c
    rw [ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  change mfderiv 𝓘(ℝ, ℝ) I (γ ∘ a) t (1 : ℝ) =
    c • mfderiv 𝓘(ℝ, ℝ) I γ (a t) (1 : ℝ)
  rw [hcomp, ha_one]
  simpa only [smul_eq_mul, mul_one] using
    map_smul (mfderiv 𝓘(ℝ, ℝ) I γ (a t)) c (1 : ℝ)

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem tailCurve_eq
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (O : M) (v : TangentSpace I O) (s₀ : ℝ) :
    let γ := intrinsicGeodesic (I := I) g hEnorm O v
    let z := intrinsicVelocityLift (I := I) g hEnorm O v s₀
    intrinsicGeodesic (I := I) g hEnorm z.proj
        ((1 - s₀) • z.snd) =
      fun t => γ ((1 - s₀) * t + s₀) := by
  dsimp only
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  have hcontinue :=
    intrinsicGeodesic_continuation (I := I) g hEnorm O v s₀
  funext t
  calc
    intrinsicGeodesic (I := I) g hEnorm
          (intrinsicVelocityLift (I := I) g hEnorm O v s₀).proj
          ((1 - s₀) •
            (intrinsicVelocityLift (I := I) g hEnorm O v s₀).snd) t =
        intrinsicGeodesic (I := I) g hEnorm
          (intrinsicVelocityLift (I := I) g hEnorm O v s₀).proj
          (t • ((1 - s₀) •
            (intrinsicVelocityLift (I := I) g hEnorm O v s₀).snd)) 1 := by
      exact
        (intrinsicGeodesic_smul (I := I) g hEnorm
          (intrinsicVelocityLift (I := I) g hEnorm O v s₀).proj
          ((1 - s₀) •
            (intrinsicVelocityLift (I := I) g hEnorm O v s₀).snd)
          t).symm
    _ = intrinsicGeodesic (I := I) g hEnorm
          (intrinsicVelocityLift (I := I) g hEnorm O v s₀).proj
          (((1 - s₀) * t) •
            (intrinsicVelocityLift (I := I) g hEnorm O v s₀).snd) 1 := by
      rw [smul_smul, mul_comm]
    _ = intrinsicGeodesic (I := I) g hEnorm
          (intrinsicVelocityLift (I := I) g hEnorm O v s₀).proj
          (intrinsicVelocityLift (I := I) g hEnorm O v s₀).snd
          ((1 - s₀) * t) := by
      exact intrinsicGeodesic_smul (I := I) g hEnorm
        (intrinsicVelocityLift (I := I) g hEnorm O v s₀).proj
        (intrinsicVelocityLift (I := I) g hEnorm O v s₀).snd
        ((1 - s₀) * t)
    _ = γ ((1 - s₀) * t + s₀) := by
      have h := congrFun hcontinue ((1 - s₀) * t)
      simpa only [γ, intrinsicVelocityLift] using h.symm

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem tailVel_one
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (O : M) (v : TangentSpace I O) (s₀ : ℝ) :
    let z := intrinsicVelocityLift (I := I) g hEnorm O v s₀
    let uTail : TangentSpace I z.proj := (1 - s₀) • z.snd
    ((intrinsicVelocityLift (I := I) g hEnorm z.proj uTail 1).snd : E) =
      (1 - s₀) •
        ((intrinsicVelocityLift (I := I) g hEnorm O v 1).snd : E) := by
  dsimp only
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  let δ : ℝ → M :=
    intrinsicGeodesic (I := I) g hEnorm
      (intrinsicVelocityLift (I := I) g hEnorm O v s₀).proj
      ((1 - s₀) •
        (intrinsicVelocityLift (I := I) g hEnorm O v s₀).snd)
  have hδ :
      δ = fun t => γ ((1 - s₀) * t + s₀) := by
    simpa only [δ, γ] using tailCurve_eq (I := I) g hEnorm O v s₀
  have hγdiff :
      MDifferentiableAt 𝓘(ℝ, ℝ) I γ ((1 - s₀) * 1 + s₀) :=
    ((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm O v).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by norm_num)
  have hvel := curveVel_affine (I := I) γ (1 - s₀) s₀ 1 hγdiff
  have htime : (1 - s₀) * 1 + s₀ = 1 := by ring
  rw [htime] at hvel
  change (curveVelocity (I := I) δ 1 : E) =
    (1 - s₀) • (curveVelocity (I := I) γ 1 : E)
  rw [hδ]
  exact hvel

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every initial segment of a finite-distance minimizing intrinsic radial
geodesic has the expected fraction of the total endpoint distance. -/
theorem minSeg_edist
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {O x : M} {r : ℝ} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen : Real.sqrt (g.inner O v v) = r)
    (hr_def : r = (riemannianEDist I O x).toReal)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    riemannianEDist I O
        (intrinsicGeodesic (I := I) g hEnorm O v s) =
      ENNReal.ofReal (s * r) := by
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    exact ENNReal.toReal_nonneg
  have hsr_nonneg : 0 ≤ s * r := mul_nonneg hs.1 hr_nonneg
  have htail_nonneg : 0 ≤ (1 - s) * r :=
    mul_nonneg (sub_nonneg.mpr hs.2) hr_nonneg
  have hleft :
      riemannianEDist I O (γ s) ≤ ENNReal.ofReal (s * r) := by
    have h :=
      intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm O v (s := 0) (t := s) hs.1
    rw [intrinsicGeodesic_zero (I := I) g hEnorm O v, hlen] at h
    simpa only [γ, sub_zero, mul_comm] using h
  have hγ_one : γ 1 = x := by
    simpa only [γ, expMapIntrinsic_def] using hexp
  have hright :
      riemannianEDist I (γ s) x ≤
        ENNReal.ofReal ((1 - s) * r) := by
    have h :=
      intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm O v (s := s) (t := 1) hs.2
    change riemannianEDist I (γ s) (γ 1) ≤ _ at h
    rw [hγ_one, hlen] at h
    simpa only [mul_comm] using h
  have hfull :
      riemannianEDist I O x = ENNReal.ofReal r := by
    rw [hr_def, ENNReal.ofReal_toReal hfin]
  have hsplit :
      ENNReal.ofReal r =
        ENNReal.ofReal (s * r) + ENNReal.ofReal ((1 - s) * r) := by
    rw [← ENNReal.ofReal_add hsr_nonneg htail_nonneg]
    congr 1
    ring
  have hsum :
      ENNReal.ofReal (s * r) + ENNReal.ofReal ((1 - s) * r) ≤
        riemannianEDist I O (γ s) +
          ENNReal.ofReal ((1 - s) * r) := by
    rw [← hsplit, ← hfull]
    have htri :
        riemannianEDist I O x ≤
          riemannianEDist I O (γ s) + riemannianEDist I (γ s) x :=
      riemannianEDist_triangle
    exact htri.trans (add_le_add_right hright _)
  exact le_antisymm hleft
    ((ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hsum)

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem minTail_edist
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {O x : M} {r : ℝ} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen : Real.sqrt (g.inner O v v) = r)
    (hr_def : r = (riemannianEDist I O x).toReal)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    riemannianEDist I
        (intrinsicGeodesic (I := I) g hEnorm O v s) x =
      ENNReal.ofReal ((1 - s) * r) := by
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    exact ENNReal.toReal_nonneg
  have hsr_nonneg : 0 ≤ s * r := mul_nonneg hs.1 hr_nonneg
  have htail_nonneg : 0 ≤ (1 - s) * r :=
    mul_nonneg (sub_nonneg.mpr hs.2) hr_nonneg
  have hleft :
      riemannianEDist I O (γ s) = ENNReal.ofReal (s * r) := by
    simpa only [γ] using
      minSeg_edist (I := I) g hEnorm v hexp hlen hr_def hfin hs
  have hγ_one : γ 1 = x := by
    simpa only [γ, expMapIntrinsic_def] using hexp
  have hright :
      riemannianEDist I (γ s) x ≤
        ENNReal.ofReal ((1 - s) * r) := by
    have h :=
      intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm O v (s := s) (t := 1) hs.2
    change riemannianEDist I (γ s) (γ 1) ≤ _ at h
    rw [hγ_one, hlen] at h
    simpa only [mul_comm] using h
  have hfull :
      riemannianEDist I O x = ENNReal.ofReal r := by
    rw [hr_def, ENNReal.ofReal_toReal hfin]
  have hsplit :
      ENNReal.ofReal r =
        ENNReal.ofReal (s * r) + ENNReal.ofReal ((1 - s) * r) := by
    rw [← ENNReal.ofReal_add hsr_nonneg htail_nonneg]
    congr 1
    ring
  have hsum :
      ENNReal.ofReal (s * r) + ENNReal.ofReal ((1 - s) * r) ≤
        ENNReal.ofReal (s * r) + riemannianEDist I (γ s) x := by
    rw [← hsplit, ← hfull, ← hleft]
    exact riemannianEDist_triangle
  exact le_antisymm hright
    ((ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp hsum)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The shifted tail of a finite-distance minimizing intrinsic geodesic is
nonconjugate at its terminal vector. -/
theorem tail_not_conj_of_min
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {O x : M} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen :
      Real.sqrt (g.inner O v v) =
        (riemannianEDist I O x).toReal)
    (hr : 0 < (riemannianEDist I O x).toReal)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    let z := intrinsicVelocityLift (I := I) g hEnorm O v s₀
    let uTail : TangentSpace I z.proj := (1 - s₀) • z.snd
    ¬ IsConjVec (I := I) g hEnorm z.proj (uTail : E) := by
  dsimp only
  classical
  let r : ℝ := (riemannianEDist I O x).toReal
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  let z₁ := intrinsicVelocityLift (I := I) g hEnorm O v 1
  let eRev : TangentSpace I z₁.proj := (-r⁻¹) • z₁.snd
  let z := intrinsicVelocityLift (I := I) g hEnorm O v s₀
  let uTail : TangentSpace I z.proj := (1 - s₀) • z.snd
  let ell : ℝ := (1 - s₀) * r
  have hr_pos : 0 < r := by simpa only [r] using hr
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hz₁x : z₁.proj = x := by
    simpa only [z₁, intrinsicVelocityLift, expMapIntrinsic_def] using hexp
  have hspeed₁ :
      g.inner z₁.proj z₁.snd z₁.snd = g.inner O v v := by
    simpa only [z₁, intrinsicVelocityLift, γ] using
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm O v 1
  have hinner : g.inner O v v = r ^ 2 := by
    have hsqrt_sq :=
      Real.sq_sqrt (gInner_self_nonneg (I := I) g O v)
    rw [hlen] at hsqrt_sq
    simpa only [r] using hsqrt_sq.symm
  have heRev_unit : g.inner z₁.proj eRev eRev = 1 := by
    dsimp only [eRev]
    rw [gInner_smul_self (I := I) g z₁.proj, hspeed₁, hinner]
    field_simp [hr_ne]
  have hback :
      intrinsicGeodesic (I := I) g hEnorm z₁.proj z₁.snd (-1) = O := by
    have hcontinue :=
      intrinsicGeodesic_continuation (I := I) g hEnorm O v 1
    have h := congrFun hcontinue (-1)
    simpa only [z₁, γ, intrinsicVelocityLift, neg_add_cancel,
      intrinsicGeodesic_zero] using h.symm
  have hscale : r • eRev = (-1 : ℝ) • z₁.snd := by
    dsimp only [eRev]
    rw [smul_smul]
    congr 1
    field_simp [hr_ne]
  have hrev_end :
      intrinsicGeodesic (I := I) g hEnorm z₁.proj eRev r = O := by
    calc
      intrinsicGeodesic (I := I) g hEnorm z₁.proj eRev r =
          intrinsicGeodesic (I := I) g hEnorm z₁.proj (r • eRev) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm z₁.proj eRev r).symm
      _ = intrinsicGeodesic (I := I) g hEnorm z₁.proj
          ((-1 : ℝ) • z₁.snd) 1 := by rw [hscale]
      _ = intrinsicGeodesic (I := I) g hEnorm z₁.proj z₁.snd (-1) :=
        intrinsicGeodesic_smul (I := I) g hEnorm z₁.proj z₁.snd (-1)
      _ = O := hback
  let γrev : ℝ → M := intrinsicGeodesic (I := I) g hEnorm z₁.proj eRev
  have hrev_min :
      ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 r) →
        η 0 = z₁.proj →
        η r = γrev r →
        arcLength (I := I) g γrev 0 r ≤
          arcLength (I := I) g η 0 r := by
    intro η hη hη0 hηr
    have hη_end : η r = O := by
      rw [hηr]
      simpa only [γrev] using hrev_end
    have hη_nonneg : 0 ≤ arcLength (I := I) g η 0 r := by
      unfold arcLength
      exact intervalIntegral.integral_nonneg hr_pos.le
        (fun _ _ => Real.sqrt_nonneg _)
    have hed :
        riemannianEDist I (η 0) (η r) ≤
          ENNReal.ofReal (arcLength (I := I) g η 0 r) :=
      riemannianEDist_le_arcLength (I := I) g hr_pos.le hη
        (fun t ht => hEnorm (η t) _)
    have hreal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hr_le : r ≤ arcLength (I := I) g η 0 r := by
      rw [hη0, hη_end, hz₁x, riemannianEDist_comm,
        ENNReal.toReal_ofReal hη_nonneg] at hreal
      simpa only [r] using hreal
    dsimp only [γrev]
    rw [arcLength_radial (I := I) g hEnorm z₁.proj eRev,
      heRev_unit, Real.sqrt_one, sub_zero, mul_one]
    exact hr_le
  have hell_pos : 0 < ell := by
    dsimp only [ell]
    exact mul_pos (sub_pos.mpr hs₀.2) hr_pos
  have hell_lt : ell < r := by
    dsimp only [ell]
    nlinarith [hs₀.1]
  have hrev_no :
      ¬ IsConjVec (I := I) g hEnorm z₁.proj (ell • eRev : E) :=
    not_conj_of_min_len (I := I) g hEnorm z₁.proj (eRev : E)
      heRev_unit r hr_pos hrev_min ⟨hell_pos, hell_lt⟩
  intro htail
  have htail_rev :=
    (conjVec_reverse (I := I) g hEnorm z.proj uTail).mp htail
  have htail_curve :
      intrinsicGeodesic (I := I) g hEnorm z.proj uTail =
        fun t => γ ((1 - s₀) * t + s₀) := by
    simpa only [z, uTail, γ] using
      tailCurve_eq (I := I) g hEnorm O v s₀
  have htail_end :
      (intrinsicVelocityLift (I := I) g hEnorm z.proj uTail 1).proj =
        z₁.proj := by
    change intrinsicGeodesic (I := I) g hEnorm z.proj uTail 1 =
      intrinsicGeodesic (I := I) g hEnorm O v 1
    rw [htail_curve]
    change γ ((1 - s₀) * 1 + s₀) = γ 1
    congr 1
    ring
  have htail_vel :
      ((intrinsicVelocityLift (I := I) g hEnorm z.proj uTail 1).snd : E) =
        (1 - s₀) • (z₁.snd : E) := by
    simpa only [z, uTail, z₁] using
      tailVel_one (I := I) g hEnorm O v s₀
  have hvec :
      -((intrinsicVelocityLift (I := I) g hEnorm z.proj uTail 1).snd : E) =
        ell • (eRev : E) := by
    rw [htail_vel]
    dsimp only [ell, eRev]
    rw [smul_smul]
    have hcoeff : -(1 - s₀) = (1 - s₀) * r * -r⁻¹ := by
      field_simp [hr_ne]
    simpa only [neg_smul] using
      congrArg (fun a : ℝ => a • (z₁.snd : E)) hcoeff
  apply hrev_no
  simpa only [htail_end, hvec] using htail_rev

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every positive radial vector on the closed shifted tail of a
finite-distance minimizing intrinsic geodesic is nonconjugate. -/
theorem tail_no_conj
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {O x : M} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen :
      Real.sqrt (g.inner O v v) =
        (riemannianEDist I O x).toReal)
    (hr : 0 < (riemannianEDist I O x).toReal)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    let z := intrinsicVelocityLift (I := I) g hEnorm O v s₀
    let uTail : TangentSpace I z.proj := (1 - s₀) • z.snd
    ∀ t ∈ Ioc (0 : ℝ) 1,
      ¬ IsConjVec (I := I) g hEnorm z.proj
        ((t • uTail : TangentSpace I z.proj) : E) := by
  dsimp only
  classical
  let r : ℝ := (riemannianEDist I O x).toReal
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  let z := intrinsicVelocityLift (I := I) g hEnorm O v s₀
  let uTail : TangentSpace I z.proj := (1 - s₀) • z.snd
  let ell : ℝ := (1 - s₀) * r
  let eTail : TangentSpace I z.proj := r⁻¹ • z.snd
  have hr_pos : 0 < r := by simpa only [r] using hr
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hfin : riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    intro htop
    simp [htop] at hr
  have hell_pos : 0 < ell := by
    dsimp only [ell]
    exact mul_pos (sub_pos.mpr hs₀.2) hr_pos
  have hspeed :
      g.inner z.proj z.snd z.snd = g.inner O v v := by
    simpa only [z, intrinsicVelocityLift, γ] using
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm O v s₀
  have hinner : g.inner O v v = r ^ 2 := by
    have hsqrt_sq :=
      Real.sq_sqrt (gInner_self_nonneg (I := I) g O v)
    rw [hlen] at hsqrt_sq
    simpa only [r] using hsqrt_sq.symm
  have heTail_unit : g.inner z.proj eTail eTail = 1 := by
    dsimp only [eTail]
    rw [gInner_smul_self (I := I) g z.proj, hspeed, hinner]
    field_simp [hr_ne]
  have hscale : ell • eTail = uTail := by
    dsimp only [ell, eTail, uTail]
    rw [smul_smul]
    congr 1
    field_simp [hr_ne]
  have hscaleE : ell • (eTail : E) = (uTail : E) :=
    congrArg (fun w : TangentSpace I z.proj => (w : E)) hscale
  have hs₀_closed : s₀ ∈ Icc (0 : ℝ) 1 := ⟨hs₀.1.le, hs₀.2.le⟩
  have htail_dist :
      riemannianEDist I z.proj x = ENNReal.ofReal ell := by
    simpa only [z, velocityLift_proj, ell, r] using
      minTail_edist (I := I) g hEnorm v hexp hlen rfl hfin hs₀_closed
  have htail_curve :
      intrinsicGeodesic (I := I) g hEnorm z.proj uTail =
        fun t => γ ((1 - s₀) * t + s₀) := by
    simpa only [z, uTail, γ] using
      tailCurve_eq (I := I) g hEnorm O v s₀
  have htail_one :
      intrinsicGeodesic (I := I) g hEnorm z.proj uTail 1 = x := by
    rw [htail_curve]
    have hγ_one : γ 1 = x := by
      simpa only [γ, expMapIntrinsic_def] using hexp
    change γ ((1 - s₀) * 1 + s₀) = x
    rw [show (1 - s₀) * 1 + s₀ = 1 by ring]
    exact hγ_one
  have heTail_end :
      intrinsicGeodesic (I := I) g hEnorm z.proj eTail ell = x := by
    calc
      intrinsicGeodesic (I := I) g hEnorm z.proj eTail ell =
          intrinsicGeodesic (I := I) g hEnorm z.proj
            (ell • eTail) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm z.proj eTail ell).symm
      _ = intrinsicGeodesic (I := I) g hEnorm z.proj uTail 1 := by
        rw [hscale]
      _ = x := htail_one
  let γtail : ℝ → M := intrinsicGeodesic (I := I) g hEnorm z.proj eTail
  have htail_min :
      ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 ell) →
        η 0 = z.proj →
        η ell = γtail ell →
        arcLength (I := I) g γtail 0 ell ≤
          arcLength (I := I) g η 0 ell := by
    intro η hη hη0 hηell
    have hη_end : η ell = x := by
      rw [hηell]
      simpa only [γtail] using heTail_end
    have hη_nonneg : 0 ≤ arcLength (I := I) g η 0 ell := by
      unfold arcLength
      exact intervalIntegral.integral_nonneg hell_pos.le
        (fun _ _ => Real.sqrt_nonneg _)
    have hed :
        riemannianEDist I (η 0) (η ell) ≤
          ENNReal.ofReal (arcLength (I := I) g η 0 ell) :=
      riemannianEDist_le_arcLength (I := I) g hell_pos.le hη
        (fun t ht => hEnorm (η t) _)
    have hreal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hell_le : ell ≤ arcLength (I := I) g η 0 ell := by
      rw [hη0, hη_end, htail_dist,
        ENNReal.toReal_ofReal hell_pos.le,
        ENNReal.toReal_ofReal hη_nonneg] at hreal
      exact hreal
    dsimp only [γtail]
    rw [arcLength_radial (I := I) g hEnorm z.proj eTail,
      heTail_unit, Real.sqrt_one, sub_zero, mul_one]
    exact hell_le
  intro t ht
  rcases eq_or_lt_of_le ht.2 with rfl | ht_lt
  · simpa only [one_smul, z, uTail] using
      tail_not_conj_of_min (I := I) g hEnorm v hexp hlen hr hs₀
  · have hcell : t * ell ∈ Ioo (0 : ℝ) ell := by
      exact ⟨mul_pos ht.1 hell_pos, (mul_lt_iff_lt_one_left hell_pos).mpr ht_lt⟩
    have hno :=
      not_conj_of_min_len (I := I) g hEnorm z.proj (eTail : E)
        heTail_unit ell hell_pos htail_min hcell
    have hvec :
        (t * ell) • (eTail : E) = t • (uTail : E) := by
      calc
        (t * ell) • (eTail : E) =
            t • (ell • (eTail : E)) := by module
        _ = t • (uTail : E) := congrArg (fun w : E => t • w) hscaleE
    intro hconj
    apply hno
    exact hvec.symm ▸ hconj

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
