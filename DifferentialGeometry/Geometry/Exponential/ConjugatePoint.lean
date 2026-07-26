import DifferentialGeometry.Geometry.Exponential.JacobiVariation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Conjugate vectors of the intrinsic exponential

The conjugate-point interface of the option-1 route (brick N of
`Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`), in the form ruled on
2026-07-19: the **definition** is differential-singularity of the intrinsic
exponential in its vector slot, and the **Jacobi characterization** is a
bridge theorem through `intrinsic_jacobi_one`.

* `IsConjVec g hEnorm p x` — the vector-slot differential of
  `expMapIntrinsic g hEnorm p` at `x` is not injective (singular, since the
  fibers are finite-dimensional of equal dimension).
* `isConjVec_iff` — singularity ⟺ a nonzero kernel vector.
* `isConjVec_iff_jacobi` — singularity ⟺ some variation Jacobi field
  `∂ₛ|₀ intrinsicGeodesic p (x + s•w) t` with `w ≠ 0` vanishes at `t = 1`.
  This is the hinge to the variational theory: by `intrinsic_jacobi` the
  variation field is Jacobi along the whole geodesic, and by `jacobi_unique`
  (`Variation/JacobiCoord.lean`) it is the *only* Jacobi field with its
  initial data.

No smallness or injectivity-radius hypothesis appears anywhere: the intrinsic
exponential is globally smooth (`intrinsicExp_smooth`), so the interface is
meaningful at every scale.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace E]

private theorem covDeriv_comp_affine
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (c d t : ℝ) :
    covDerivAlong (I := I) g
        (fun s => γ (c * s + d)) (fun s => V (c * s + d)) t =
      c • covDerivAlong (I := I) g γ V (c * t + d) := by
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [← map_smul]
  congr 1
  have hrep :
      chartRepAt (I := I) (fun s => γ (c * s + d))
          (fun s => V (c * s + d)) t =
        fun s => chartRepAt (I := I) γ V (c * t + d) (c * s + d) := rfl
  have hcurve :
      chartCurve (I := I) (γ (c * t + d)) (fun s => γ (c * s + d)) =
        fun s => chartCurve (I := I) (γ (c * t + d)) γ (c * s + d) := rfl
  rw [hrep, chartCovDerivAlong_def, chartCovDerivAlong_def, hcurve]
  have hderiv (f : ℝ → E) :
      deriv (fun s => f (c * s + d)) t = c • deriv f (c * t + d) := by
    calc
      deriv (fun s => f (c * s + d)) t =
          deriv (fun s => (fun r => f (r + d)) (c * s)) t := rfl
      _ = c • deriv (fun r => f (r + d)) (c * t) :=
        deriv_comp_mul_left c (fun r : ℝ => f (r + d)) t
      _ = c • deriv f (c * t + d) := by rw [deriv_comp_add_const]
  rw [hderiv, hderiv,
    ChartChristoffel.contraction_smul_left, smul_add]

private theorem curveVelocity_comp_affine
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

private theorem jacobi_comp_affine
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) (c d : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hJ : IsJacobiAlong (I := I) g γ J) :
    IsJacobiAlong (I := I) g
      (fun s => γ (c * s + d)) (fun s => J (c * s + d)) := by
  intro t
  let δ : ℝ → M := fun s => γ (c * s + d)
  let L : ∀ s, TangentSpace I (δ s) := fun s => J (c * s + d)
  let DJ : ∀ s, TangentSpace I (γ s) :=
    fun s => covDerivAlong (I := I) g γ J s
  have hDL : (fun s => covDerivAlong (I := I) g δ L s) =
      fun s => c • DJ (c * s + d) := by
    funext s
    exact covDeriv_comp_affine (I := I) g γ J c d s
  have hD2 :
      covDerivAlong (I := I) g δ
          (fun s => covDerivAlong (I := I) g δ L s) t =
        (c * c) • covDerivAlong (I := I) g γ DJ (c * t + d) := by
    rw [hDL]
    rw [covDerivAlong_smul]
    rw [covDeriv_comp_affine (I := I) g γ DJ c d t, smul_smul]
  have hvel :
      curveVelocity (I := I) δ t =
        c • curveVelocity (I := I) γ (c * t + d) := by
    exact curveVelocity_comp_affine (I := I) γ c d t
      (hγ.contMDiffAt.mdifferentiableAt (by simp))
  change
    covDerivAlong (I := I) g δ
        (fun s => covDerivAlong (I := I) g δ L s) t +
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
          (δ t))
        (L t) (curveVelocity (I := I) δ t)
        (curveVelocity (I := I) δ t) = 0
  rw [hD2, hvel]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  rw [← smul_add, hJ (c * t + d), smul_zero]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem intrinsicGeodesic_smooth
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : TangentSpace I p) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (intrinsicGeodesic (I := I) g hEnorm p u) := by
  have hvar := intrinsicVar_smooth (I := I) g hEnorm p (u : E) 0
  have hincl : ContMDiff 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => ((0 : ℝ), t)) :=
    contMDiff_const.prodMk contMDiff_id
  simpa only [Function.comp_apply, smul_zero, add_zero] using hvar.comp hincl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem intrinsicGeodesic_reverse
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : TangentSpace I p) :
    let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
    intrinsicGeodesic (I := I) g hEnorm z.proj (-z.snd) =
      fun t => intrinsicGeodesic (I := I) g hEnorm p u (1 - t) := by
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
  let δ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm z.proj (-z.snd)
  let rev : ℝ → M := fun t => γ ((-1 : ℝ) * t + 1)
  have hγ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm p u
  have hδ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ δ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm z.proj (-z.snd)
  have hrev_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ rev := by
    have ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (-1 : ℝ) * t + 1) :=
      contMDiff_const.mul contMDiff_id |>.add contMDiff_const
    exact hγ_inf.comp ha
  have hδ_geo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
      (I := I) g δ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm z.proj (-z.snd)
  have hγ_geo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
      (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
  have hrev_geo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
      (I := I) g rev := by
    intro t
    exact
      DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_comp_affine
        (I := I) (hγ_geo ((-1 : ℝ) * t + 1))
  have hfoot : δ 0 = rev 0 := by
    dsimp only [δ, rev]
    rw [intrinsicGeodesic_zero]
    dsimp only [z, γ, intrinsicVelocityLift]
    norm_num
  have hδvel :
      (curveVelocity (I := I) δ 0 : E) = (-z.snd : E) := by
    simpa only [curveVelocity, δ] using
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm z.proj (-z.snd)
  have hrevvel :
      (curveVelocity (I := I) rev 0 : E) = (-z.snd : E) := by
    have h := curveVelocity_comp_affine (I := I) γ (-1) 1 0
      (hγ_inf.contMDiffAt.mdifferentiableAt (by simp))
    have h' : curveVelocity (I := I) rev 0 =
        (-1 : ℝ) • curveVelocity (I := I) γ 1 := by
      change curveVelocity (I := I) rev 0 =
        (-1 : ℝ) • curveVelocity (I := I) γ ((-1 : ℝ) * 0 + 1) at h
      have ht : (-1 : ℝ) * 0 + 1 = 1 := by norm_num
      rw [ht] at h
      exact h
    rw [h', neg_one_smul]
    rfl
  have hvel : (curveVelocity (I := I) δ 0 : E) =
      (curveVelocity (I := I) rev 0 : E) :=
    hδvel.trans hrevvel.symm
  have heq : δ = rev :=
    isGeodesic_eq_of_initial (I := I) g hδ_geo hrev_geo
      hδ_inf.continuous hrev_inf.continuous hfoot hvel
  change δ = fun t => γ (1 - t)
  rw [heq]
  funext t
  dsimp only [rev]
  congr 1
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem exp_pair_reverse
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a : TangentSpace I p)
    (b : E) :
    let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
    g.inner z.proj
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from w))
          (u : E) (a : E))
        b =
      g.inner p a
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm z.proj
            (show TangentSpace I z.proj from w))
          (-z.snd : E) b) := by
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
  let δ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm z.proj (-z.snd)
  generalize hrev_def : (fun t => γ ((-1 : ℝ) * t + 1)) = rev
  have hδrev : δ = rev := by
    have h := intrinsicGeodesic_reverse (I := I) g hEnorm p u
    change δ = fun t => γ (1 - t) at h
    rw [h, ← hrev_def]
    funext t
    congr 1
    ring
  let F : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p (u + s • a) t
  let G : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm z.proj
      ((show TangentSpace I z.proj from -z.snd) +
        s • (show TangentSpace I z.proj from b)) t
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s t) 0 (1 : ℝ)
  let K : ∀ t : ℝ, TangentSpace I (δ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => G s t) 0 (1 : ℝ)
  have hF_inf :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => F q.1 q.2) := by
    simpa only [F] using intrinsicVar_smooth (I := I) g hEnorm p (u : E) (a : E)
  have hG_inf :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => G q.1 q.2) := by
    simpa only [G] using
      intrinsicVar_smooth (I := I) g hEnorm z.proj (-z.snd : E) b
  have hF_smooth : IsSmoothVariation (I := I) F :=
    hF_inf.of_le ENat.LEInfty.out
  have hG_smooth : IsSmoothVariation (I := I) G :=
    hG_inf.of_le ENat.LEInfty.out
  have hγ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm p u
  have hδ_inf : ContMDiff 𝓘(ℝ, ℝ) I ∞ δ :=
    intrinsicGeodesic_smooth (I := I) g hEnorm z.proj (-z.snd)
  have hJdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t := by
    have h := variationField_chartRep_differentiableAt
      (I := I) g F hF_smooth t
    have hF0 : (fun v => F 0 v) = γ := by
      funext v
      simp only [F, γ, zero_smul, add_zero]
    rw [hF0] at h
    simpa only [F, J] using h
  have hDJdiff (t : ℝ) :
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ J s) t) t := by
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I) g F hF_smooth t
    have hF0 : (fun v => F 0 v) = γ := by
      funext v
      simp only [F, γ, zero_smul, add_zero]
    rw [hF0] at h
    simpa only [F, J] using h
  have hKdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) δ K t) t := by
    have h := variationField_chartRep_differentiableAt
      (I := I) g G hG_smooth t
    have hG0 : (fun v => G 0 v) = δ := by
      funext v
      simp only [G, δ, zero_smul, add_zero]
    rw [hG0] at h
    simpa only [G, K] using h
  have hDKdiff (t : ℝ) :
      DifferentiableAt ℝ
        (chartRepAt (I := I) δ
          (fun s => covDerivAlong (I := I) g δ K s) t) t := by
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I) g G hG_smooth t
    have hG0 : (fun v => G 0 v) = δ := by
      funext v
      simp only [G, δ, zero_smul, add_zero]
    rw [hG0] at h
    simpa only [G, K] using h
  have hJacJ : IsJacobiAlong (I := I) g γ J := by
    simpa only [γ, J] using
      intrinsic_jacobi (I := I) g hEnorm p (u : E) (a : E)
  have hJacK : IsJacobiAlong (I := I) g δ K := by
    simpa only [δ, K, G] using
      intrinsic_jacobi (I := I) g hEnorm z.proj (-z.snd : E) b
  cases hδrev
  let Hrev : ℝ → ℝ → M := fun s t => F s ((-1 : ℝ) * t + 1)
  let JR : ∀ t : ℝ, TangentSpace I (δ t) :=
    fun t => J ((-1 : ℝ) * t + 1)
  have hHrev_inf :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => Hrev q.1 q.2) := by
    have hflip :
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
          (fun q : ℝ × ℝ => (q.1, (-1 : ℝ) * q.2 + 1)) :=
      contMDiff_fst.prodMk
        (contMDiff_const.mul contMDiff_snd |>.add contMDiff_const)
    exact hF_inf.comp hflip
  have hHrev_smooth : IsSmoothVariation (I := I) Hrev :=
    hHrev_inf.of_le ENat.LEInfty.out
  have hJRdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) δ JR t) t := by
    have h := variationField_chartRep_differentiableAt
      (I := I) g Hrev hHrev_smooth t
    have hH0 : (fun v => Hrev 0 v) = δ := by
      rw [← hrev_def]
      funext v
      simp only [Hrev, F, γ, zero_smul, add_zero]
    rw [hH0] at h
    simpa only [Hrev, JR] using h
  have hDJRdiff (t : ℝ) :
      DifferentiableAt ℝ
        (chartRepAt (I := I) δ
          (fun s => covDerivAlong (I := I) g δ JR s) t) t := by
    have h := variationField_covDeriv_chartRep_differentiableAt
      (I := I) g Hrev hHrev_smooth t
    have hH0 : (fun v => Hrev 0 v) = δ := by
      rw [← hrev_def]
      funext v
      simp only [Hrev, F, γ, zero_smul, add_zero]
    rw [hH0] at h
    simpa only [Hrev, JR] using h
  have hJacJR : IsJacobiAlong (I := I) g δ JR := by
    rw [← hrev_def]
    simpa only [JR, Hrev, F] using
      jacobi_comp_affine (I := I) g γ J (-1) 1 hγ_inf hJacJ
  have hWderiv (t : ℝ) :
      HasDerivAt (jacobiWronskian (I := I) g δ K JR) 0 t :=
    hasDerivAt_wronsk (I := I) (n := ∞) (by simp) g δ K JR t hδ_inf
      (hKdiff t) (hJRdiff t) (hDKdiff t) (hDJRdiff t)
      (hJacK t) (hJacJR t)
  have hWcont :
      ContinuousOn (jacobiWronskian (I := I) g δ K JR)
        (Icc (0 : ℝ) 1) := by
    intro t _
    exact (hWderiv t).continuousAt.continuousWithinAt
  have hWconst := constant_of_has_deriv_right_zero hWcont
    (fun t ht => (hWderiv t).hasDerivWithinAt)
  have hW10 :
      jacobiWronskian (I := I) g δ K JR 1 =
        jacobiWronskian (I := I) g δ K JR 0 :=
    hWconst 1 (by norm_num)
  have hJ0 : J 0 = 0 := by
    have hconst :
        (fun s : ℝ => F s 0) = fun _ : ℝ => p := by
      funext s
      exact intrinsicGeodesic_zero (I := I) g hEnorm p _
    change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s 0) 0 (1 : ℝ) = 0
    rw [hconst, mfderiv_const]
    rfl
  have hDJ0 :
      (covDerivAlong (I := I) g γ J 0 : E) = (a : E) := by
    simpa only [γ, J] using
      intrinsic_jacobi_d0 (I := I) g hEnorm p (u : E) (a : E)
  have hJ1 :
      (J 1 : E) =
        mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from w))
          (u : E) (a : E) := by
    simpa only [γ, J] using
      intrinsic_jacobi_one (I := I) g hEnorm p (u : E) (a : E)
  have hK0 : K 0 = 0 := by
    have hconst :
        (fun s : ℝ => G s 0) = fun _ : ℝ => z.proj := by
      funext s
      exact intrinsicGeodesic_zero (I := I) g hEnorm z.proj _
    change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => G s 0) 0 (1 : ℝ) = 0
    rw [hconst, mfderiv_const]
    rfl
  have hDK0 :
      (covDerivAlong (I := I) g δ K 0 : E) = b := by
    simpa only [K, G] using
      intrinsic_jacobi_d0 (I := I) g hEnorm z.proj (-z.snd : E) b
  have hK1 :
      (K 1 : E) =
        mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm z.proj
            (show TangentSpace I z.proj from w))
          (-z.snd : E) b := by
    simpa only [K, G] using
      intrinsic_jacobi_one (I := I) g hEnorm z.proj (-z.snd : E) b
  have hDJR (t : ℝ) :
      covDerivAlong (I := I) g δ JR t =
        (-1 : ℝ) • covDerivAlong (I := I) g γ J ((-1 : ℝ) * t + 1) := by
    rw [← hrev_def]
    simpa only [JR] using
      covDeriv_comp_affine (I := I) g γ J (-1) 1 t
  have hJR0 : JR 0 = J 1 := by
    change J ((-1 : ℝ) * 0 + 1) = J 1
    have ht : (-1 : ℝ) * 0 + 1 = 1 := by norm_num
    rw [ht]
  have hJR1 : JR 1 = J 0 := by
    change J ((-1 : ℝ) * 1 + 1) = J 0
    have ht : (-1 : ℝ) * 1 + 1 = 0 := by norm_num
    rw [ht]
  have hDJR1 :
      covDerivAlong (I := I) g δ JR 1 =
        -covDerivAlong (I := I) g γ J 0 := by
    have h := hDJR 1
    have ht : (-1 : ℝ) * 1 + 1 = 0 := by norm_num
    rw [ht] at h
    simpa only [neg_one_smul] using h
  have hδ0 : δ 0 = z.proj := by
    simpa only [δ] using
      intrinsicGeodesic_zero (I := I) g hEnorm z.proj (-z.snd)
  have hδ1 : δ 1 = p := by
    have h := congrFun hrev_def 1
    have ht : (-1 : ℝ) * 1 + 1 = 0 := by norm_num
    rw [ht] at h
    have hγ0 : γ 0 = p := by
      simpa only [γ] using
        intrinsicGeodesic_zero (I := I) g hEnorm p u
    exact h.symm.trans hγ0
  have hpair :
      g.inner p (K 1) a = g.inner z.proj b (J 1) := by
    simp only [jacobiWronskian] at hW10
    rw [hJR1, hJ0, hDJR1, hDJ0, hK0, hDK0, hJR0] at hW10
    have hz1 :
        g.inner (δ 1) (covDerivAlong (I := I) g δ K 1)
            (0 : TangentSpace I (δ 1)) = 0 :=
      map_zero _
    have hz0 :
        g.inner (δ 0) (0 : TangentSpace I (δ 0))
            (covDerivAlong (I := I) g δ JR 0) = 0 := by
      rw [map_zero]
      rfl
    have hWsimple :
        0 - g.inner (δ 1) (K 1) (-a) =
          g.inner (δ 0) b (J 1) - 0 := by
      calc
        0 - g.inner (δ 1) (K 1) (-a) =
            g.inner (δ 1) (covDerivAlong (I := I) g δ K 1)
                (0 : TangentSpace I (δ 1)) -
              g.inner (δ 1) (K 1) (-a) := by rw [hz1]
        _ =
            g.inner (δ 0) b (J 1) -
              g.inner (δ 0) (0 : TangentSpace I (δ 0))
                (covDerivAlong (I := I) g δ JR 0) := hW10
        _ = g.inner (δ 0) b (J 1) - 0 := by rw [hz0]
    rw [hδ1, hδ0] at hWsimple
    have hneg1 :
        g.inner p (K 1) (-a) = -g.inner p (K 1) a :=
      map_neg (g.inner p (K 1)) a
    rw [hneg1, sub_zero, zero_sub, neg_neg] at hWsimple
    exact hWsimple
  calc
    g.inner z.proj
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from w))
          (u : E) (a : E))
        b =
      g.inner z.proj b (J 1) := by rw [hJ1, g.symm]
    _ = g.inner p (K 1) a := hpair.symm
    _ =
      g.inner p a
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapIntrinsic (I := I) g hEnorm z.proj
            (show TangentSpace I z.proj from w))
          (-z.snd : E) b) := by rw [hK1, g.symm]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Conjugate vector.**  `x` is conjugate for the exponential at `p` when
the vector-slot differential of the intrinsic exponential at `x` is not
injective. -/
def IsConjVec
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (x : E) : Prop :=
  ¬ Function.Injective fun w : E =>
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from b)) x w

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Singularity ⟺ nonzero kernel vector.** -/
theorem isConjVec_iff
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (x : E) :
    IsConjVec (I := I) g hEnorm p x ↔
      ∃ w : E, w ≠ 0 ∧
        mfderiv 𝓘(ℝ, E) I
          (fun b : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from b)) x w = 0 := by
  classical
  set f := mfderiv 𝓘(ℝ, E) I
    (fun b : E => expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from b)) x with hf
  have hker : Function.Injective (fun w : E => f w) ↔
      ∀ w : E, f w = 0 → w = 0 := by
    constructor
    · intro hinj w hw
      have h0 : f w = f 0 := by rw [hw, map_zero]
      exact hinj h0
    · intro hker a b hab
      have hab' : f a = f b := hab
      have hsub : f (a - b) = 0 := by
        calc f (a - b) = f a - f b := map_sub f a b
          _ = 0 := by rw [hab', sub_self]
      exact sub_eq_zero.mp (hker _ hsub)
  unfold IsConjVec
  rw [← hf, hker]
  push Not
  constructor
  · rintro ⟨w, hw0, hwne⟩
    exact ⟨w, hwne, hw0⟩
  · rintro ⟨w, hwne, hw0⟩
    exact ⟨w, hw0, hwne⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Conjugacy of an intrinsic exponential vector is invariant under reversing
the corresponding unit-time geodesic segment. -/
theorem conjVec_reverse
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : TangentSpace I p) :
    IsConjVec (I := I) g hEnorm p (u : E) ↔
      let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
      IsConjVec (I := I) g hEnorm z.proj (-z.snd : E) := by
  classical
  let z := intrinsicVelocityLift (I := I) g hEnorm p u 1
  let A : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I
      (fun w : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from w))
      (u : E)
  let B : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I
      (fun w : E => expMapIntrinsic (I := I) g hEnorm z.proj
        (show TangentSpace I z.proj from w))
      (-z.snd : E)
  change (¬ Function.Injective A) ↔ ¬ Function.Injective B
  apply not_congr
  constructor
  · intro hA x y hxy
    have hAsurj : Function.Surjective A :=
      LinearMap.surjective_of_injective hA
    have hB0 : B (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ := hAsurj (x - y)
    have hsquare :
        g.inner z.proj (x - y) (x - y) = 0 := by
      calc
        g.inner z.proj (x - y) (x - y) =
            g.inner z.proj (A a) (x - y) := by rw [ha]
        _ = g.inner p a (B (x - y)) := by
          simpa only [A, B, z] using
            exp_pair_reverse (I := I) g hEnorm p u
              (show TangentSpace I p from a) (x - y)
        _ = 0 := by
          rw [hB0]
          exact map_zero _
    have hsub : x - y = 0 := by
      by_contra hne
      exact (ne_of_gt (g.pos z.proj (x - y) hne)) hsquare
    exact sub_eq_zero.mp hsub
  · intro hB x y hxy
    have hBsurj : Function.Surjective B :=
      LinearMap.surjective_of_injective hB
    have hA0 : A (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨b, hb⟩ := hBsurj (x - y)
    have hsquare :
        g.inner p (x - y) (x - y) = 0 := by
      calc
        g.inner p (x - y) (x - y) =
            g.inner p (x - y) (B b) := by rw [hb]
        _ = g.inner z.proj (A (x - y)) b := by
          symm
          simpa only [A, B, z] using
            exp_pair_reverse (I := I) g hEnorm p u
              (show TangentSpace I p from x - y) b
        _ = 0 := by
          rw [hA0]
          have hz :
              g.inner z.proj (0 : TangentSpace I z.proj) b = 0 := by
            rw [map_zero]
            rfl
          exact hz
    have hsub : x - y = 0 := by
      by_contra hne
      exact (ne_of_gt (g.pos p (x - y) hne)) hsquare
    exact sub_eq_zero.mp hsub

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Jacobi characterization of conjugate vectors.**  `x` is conjugate iff
some variation Jacobi field with nonzero direction `w` vanishes at time one:
`∂ₛ|₀ intrinsicGeodesic p (x + s•w) 1 = 0`.  Bridge through
`intrinsic_jacobi_one`. -/
theorem isConjVec_iff_jacobi
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (x : E) :
    IsConjVec (I := I) g hEnorm p x ↔
      ∃ w : E, w ≠ 0 ∧
        mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + s • w) 1) 0 (1 : ℝ) = 0 := by
  rw [isConjVec_iff (I := I) g hEnorm p x]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [intrinsic_jacobi_one (I := I) g hEnorm p x w]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The variation Jacobi field vanishes at time zero.**  Every geodesic of
the variation starts at `p`, so the `s`-derivative at `t = 0` is zero.  With
`isConjVec_iff_jacobi` this gives the classical phrasing: a conjugate vector
carries a nontrivial Jacobi field vanishing at both ends of the segment. -/
theorem jacobiVar_zero
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (x w : E) :
    mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x + s • w) 0) 0 (1 : ℝ) = 0 := by
  have hconst : (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from x + s • w) 0) = fun _ : ℝ => p := by
    funext s
    exact intrinsicGeodesic_zero (I := I) g hEnorm p _
  rw [hconst, mfderiv_const]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Rescaling the launch vector and evaluating at time one agrees, after
differentiation, with evaluating the rescaled variation at the original
time. -/
theorem jacobiVar_smul
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u w : E) {c : ℝ} (hc : c ≠ 0) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c) 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1) 0 (1 : ℝ) := by
  have hfun :
      (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u + s • (c⁻¹ • w)) c) =
        fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1 := by
    funext s
    have hscale : c • (u + s • (c⁻¹ • w)) = c • u + s • w := by
      rw [smul_add, smul_smul, smul_smul]
      congr 1
      field_simp
    calc
      intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c =
        intrinsicGeodesic (I := I) g hEnorm p
          (c • (show TangentSpace I p from u + s • (c⁻¹ • w))) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c).symm
      _ = intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1 := by
        exact congrArg
          (fun z : E => intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from z) 1)
          hscale
  rw [hfun]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A conjugate vector at `c • u` produces a nontrivial intrinsic Jacobi
variation along the geodesic launched by `u` that vanishes at time `c`. -/
theorem conjVec_jacobi_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E) {c : ℝ} (hc : c ≠ 0)
    (hconj : IsConjVec (I := I) g hEnorm p (c • u)) :
    ∃ z : E, z ≠ 0 ∧
      mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • z) c) 0 (1 : ℝ) = 0 := by
  rw [isConjVec_iff_jacobi (I := I) g hEnorm p (c • u)] at hconj
  obtain ⟨w, hw, hwend⟩ := hconj
  refine ⟨c⁻¹ • w, smul_ne_zero (inv_ne_zero hc) hw, ?_⟩
  rw [jacobiVar_smul (I := I) g hEnorm p u w hc]
  exact hwend

end Riemannian
end Geometry
end DifferentialGeometry
