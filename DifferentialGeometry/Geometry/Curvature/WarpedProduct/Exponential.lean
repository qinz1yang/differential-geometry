import DifferentialGeometry.Geometry.Curvature.WarpedProduct.Vertical
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Metric.WarpedProduct.Exponential
import DifferentialGeometry.Geometry.Connection.WarpedProduct
import DifferentialGeometry.Geometry.Curvature.WarpedProduct.Mixed
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

private theorem halfLineT2 : T2Space (EuclideanHalfSpace 1) := by
  unfold EuclideanHalfSpace
  infer_instance
attribute [local instance] halfLineT2

private def halfLineMetric : SmoothRiemannianMetric (𝓡∂ 1) (EuclideanHalfSpace 1) :=
  (euclideanMetric (E := EuclideanSpace ℝ (Fin 1))).pullback
    (𝓡∂ 1) (𝓡∂ 1).contMDiff (fun _ => by
      rw [(𝓡∂ 1).hasMFDerivAt.mfderiv]
      exact Function.injective_id)

private theorem halfLineMetric_inner (p : EuclideanHalfSpace 1)
    (v w : EuclideanSpace ℝ (Fin 1)) : halfLineMetric.inner p v w = v 0 * w 0 := by
  unfold halfLineMetric
  erw [SmoothRiemannianMetric.pullback_inner,
    (𝓡∂ 1).hasMFDerivAt.mfderiv, euclideanMetric_inner]
  change inner ℝ v w = v 0 * w 0
  simp [PiLp.inner_apply, mul_comm]

private def halfLineUnit : Cₛ^∞⟮𝓡∂ 1; EuclideanSpace ℝ (Fin 1),
    (TangentSpace (𝓡∂ 1) : EuclideanHalfSpace 1 → Type _)⟯ where
  toFun _ := WithLp.toLp 2 (fun _ => (1 : ℝ))
  contMDiff_toFun := by
    intro x
    erw [contMDiffAt_section]
    simp only [trivializationAt_model_space_apply]
    exact contMDiffAt_const

private theorem halfLineUnit_parallel (p : EuclideanHalfSpace 1)
    (v : TangentSpace (𝓡∂ 1) p) : (LeviCivita halfLineMetric) halfLineUnit p v = 0 := by
  have h := (leviCivitaConnectionOfMetric_isMetricCompatible halfLineMetric).mvfderiv_inner v
    halfLineUnit.mdifferentiableAt halfLineUnit.mdifferentiableAt
  have he : (fun x => halfLineMetric.inner x (halfLineUnit x) (halfLineUnit x)) =
      fun _ => (1 : ℝ) := by
    funext x
    erw [halfLineMetric_inner]
    change (1 : ℝ) * 1 = 1
    exact mul_one 1
  rw [he, mvfderiv_const] at h
  erw [halfLineMetric_inner, halfLineMetric_inner] at h
  let a : EuclideanSpace ℝ (Fin 1) := (LeviCivita halfLineMetric) halfLineUnit p v
  change (0 : ℝ) = a 0 * 1 + 1 * a 0 at h
  have hz : a 0 = 0 := by linarith
  change a = 0
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi, PiLp.zero_apply] using hz

open DifferentialGeometry.Geometry.Operator

private def halfLineDepth (p : EuclideanHalfSpace 1) : ℝ := p.val 0

private theorem halfLineDepth_smooth :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ halfLineDepth :=
  (PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0).contDiff.contMDiff.comp
    (𝓡∂ 1).contMDiff

private theorem halfLineDepth_mfderiv (p : EuclideanHalfSpace 1) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) halfLineDepth p =
      PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0 := by
  have hd := (PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0).hasMFDerivAt.comp p
    (𝓡∂ 1).hasMFDerivAt
  change HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, ℝ) halfLineDepth p
    ((PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0).comp
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))) at hd
  exact hd.mfderiv.trans (by ext v; rfl)

private theorem halfLine_comp_depth_deriv
    {φ : ℝ → ℝ} {d : ℝ} (p : EuclideanHalfSpace 1)
    (hφ : HasDerivAt φ d (halfLineDepth p)) (v : EuclideanSpace ℝ (Fin 1)) :
    mvfderiv (𝓡∂ 1) (fun q => φ (halfLineDepth q)) p v = d * v 0 := by
  have hc := mvfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓡∂ 1)
    (f := halfLineDepth) (g := φ) p hφ.differentiableAt.mdifferentiableAt
    (halfLineDepth_smooth.mdifferentiable (by simp) p) v
  erw [halfLineDepth_mfderiv] at hc
  change mvfderiv (𝓡∂ 1) (fun q => φ (halfLineDepth q)) p v =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (halfLineDepth p) (v 0) at hc
  erw [mfderiv_eq_fderiv, hφ.hasFDerivAt.fderiv] at hc
  change mvfderiv (𝓡∂ 1) (fun q => φ (halfLineDepth q)) p v = v 0 * d at hc
  exact hc.trans (mul_comm _ _)

private def halfLineExp (κ : ℝ) (p : EuclideanHalfSpace 1) : ℝ :=
  Real.exp (-κ * halfLineDepth p)

private theorem halfLineExp_smooth (κ : ℝ) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (halfLineExp κ) :=
  Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul halfLineDepth_smooth)

private theorem halfLineExp_deriv (κ : ℝ) (p : EuclideanHalfSpace 1)
    (v : EuclideanSpace ℝ (Fin 1)) :
    mvfderiv (𝓡∂ 1) (halfLineExp κ) p v =
      (-κ * halfLineExp κ p) * v 0 := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-κ * s))
      (-κ * Real.exp (-κ * halfLineDepth p)) (halfLineDepth p) := by
    simpa only [id_eq, mul_one, mul_comm] using
      ((hasDerivAt_id (halfLineDepth p)).const_mul (-κ)).exp
  exact halfLine_comp_depth_deriv p hd v

private theorem halfLineExp_grad (κ : ℝ) (p : EuclideanHalfSpace 1) :
    gradFun halfLineMetric (halfLineExp κ) p =
      (-κ * halfLineExp κ p) • halfLineUnit p := by
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq
    halfLineMetric
  intro w
  rw [gradFun_metricDual_mvfderiv]
  erw [halfLineExp_deriv, halfLineMetric_inner]
  let w₀ : EuclideanSpace ℝ (Fin 1) := w
  change (-κ * halfLineExp κ p) * w₀ 0 =
    ((-κ * halfLineExp κ p) * 1) * w₀ 0
  rw [mul_one]

private theorem halfLineExp_coefficient_deriv (κ : ℝ) (p : EuclideanHalfSpace 1)
    (v : EuclideanSpace ℝ (Fin 1)) :
    mvfderiv (𝓡∂ 1) (fun q => -κ * halfLineExp κ q) p v =
      (κ ^ 2 * halfLineExp κ p) * v 0 := by
  have hd : HasDerivAt (fun s : ℝ => -κ * Real.exp (-κ * s))
      (-κ * (Real.exp (-κ * halfLineDepth p) * (-κ))) (halfLineDepth p) := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (halfLineDepth p)).const_mul (-κ)).exp).const_mul (-κ)
  have hh := halfLine_comp_depth_deriv p hd v
  change mvfderiv (𝓡∂ 1) (fun q => -κ * halfLineExp κ q) p v =
    (-κ * (halfLineExp κ p * (-κ))) * v 0 at hh
  rw [hh]
  ring

private theorem halfLineExp_cov_grad (κ : ℝ) (p : EuclideanHalfSpace 1)
    (v : EuclideanSpace ℝ (Fin 1)) :
    (LeviCivita halfLineMetric) (gradFun halfLineMetric (halfLineExp κ)) p v =
      (κ ^ 2 * Real.exp (-κ * p.val 0) * v 0) • halfLineUnit p := by
  let a : EuclideanHalfSpace 1 → ℝ := fun q => -κ * halfLineExp κ q
  let σ : (q : EuclideanHalfSpace 1) → TangentSpace (𝓡∂ 1) q :=
    fun q => halfLineUnit q
  let C : CovariantDerivative (𝓡∂ 1) (EuclideanSpace ℝ (Fin 1))
      (TangentSpace (𝓡∂ 1) : EuclideanHalfSpace 1 → Type _) :=
    LeviCivita halfLineMetric
  let v₀ : TangentSpace (𝓡∂ 1) p := v
  let b : ℝ := κ ^ 2 * halfLineExp κ p * v 0
  have hg : gradFun halfLineMetric (halfLineExp κ) = a • σ :=
    funext (halfLineExp_grad κ)
  have hcoeff : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, ℝ) a p :=
    (contMDiff_const.mul (halfLineExp_smooth κ)).mdifferentiable (by simp) p
  have hσ : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1).tangent (T% σ) p :=
    halfLineUnit.mdifferentiableAt
  have hleib : C (a • σ) p = a p • C σ p +
      (mvfderiv (𝓡∂ 1) a p).smulRight (σ p) :=
    C.isCovariantDerivativeOnUniv.leibniz hσ hcoeff
  have hv := congrArg
    (fun L : TangentSpace (𝓡∂ 1) p →L[ℝ] TangentSpace (𝓡∂ 1) p => L v₀) hleib
  change C (a • σ) p v₀ =
    a p • (C σ p v₀) + (mvfderiv (𝓡∂ 1) a p v₀) • σ p at hv
  have hparallel : C σ p v₀ = 0 := halfLineUnit_parallel p v₀
  have hda : mvfderiv (𝓡∂ 1) a p v₀ = b :=
    halfLineExp_coefficient_deriv κ p v
  have hr := congrArg₂
    (fun (w : TangentSpace (𝓡∂ 1) p) (c : ℝ) => a p • w + c • σ p)
    hparallel hda
  have hz : a p • (0 : TangentSpace (𝓡∂ 1) p) + b • σ p = b • σ p := by
    rw [smul_zero, zero_add]
  have htransport := congrArg
    (fun X : (q : EuclideanHalfSpace 1) → TangentSpace (𝓡∂ 1) q => C X p v₀) hg
  exact htransport.trans (hv.trans (hr.trans hz))

open DifferentialGeometry.Geometry.Curvature

private theorem halfLineExp_mixed_curvature
    {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanHalfSpace 1 × N) (u z : EuclideanSpace ℝ (Fin 1))
    (v w : TangentSpace J p.2) :
    metricRm04StandardAt
      (halfLineMetric.warpedProduct h (halfLineExp κ) (halfLineExp_smooth κ)
        (fun q => Real.exp_pos (-κ * halfLineDepth q)))
      p (u, 0) (0, v) (0, w) (z, 0) =
      -κ ^ 2 * Real.exp (-2 * κ * p.1.val 0) * u 0 * z 0 * h.inner p.2 v w := by
  have hm := metricRm04StandardAt_warpedProduct_mixed halfLineMetric h
    (halfLineExp κ) (halfLineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * halfLineDepth q)) p u z v w
  have hg := halfLineExp_cov_grad κ p.1 u
  have hp := congrArg
    (fun a : TangentSpace (𝓡∂ 1) p.1 => halfLineMetric.inner p.1 z a) hg
  have hs : halfLineMetric.inner p.1 z
      ((κ ^ 2 * Real.exp (-κ * p.1.val 0) * u 0) • halfLineUnit p.1) =
      z 0 * (κ ^ 2 * Real.exp (-κ * p.1.val 0) * u 0) := by
    erw [halfLineMetric_inner]
    change z 0 * ((κ ^ 2 * Real.exp (-κ * p.1.val 0) * u 0) * 1) = _
    rw [mul_one]
  have he : Real.exp (-κ * p.1.val 0) ^ 2 = Real.exp (-2 * κ * p.1.val 0) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine hm.trans ?_
  rw [hp.trans hs]
  change -(Real.exp (-κ * p.1.val 0) * h.inner p.2 v w) *
    (z 0 * (κ ^ 2 * Real.exp (-κ * p.1.val 0) * u 0)) = _
  rw [← he]
  ring

namespace DifferentialGeometry.Geometry.Curvature

theorem metricRm04StandardAt_exponentialWarpedEnd_mixed
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (κ : ℝ)
    (p : M × EuclideanHalfSpace 1) (u z : EuclideanSpace ℝ (Fin 1))
    (v w : TangentSpace I p.1) :
    metricRm04StandardAt (g.exponentialWarpedEnd κ) p
      (0, u) (v, 0) (w, 0) (0, z) =
      -κ ^ 2 * Real.exp (-2 * κ * p.2.val 0) * u 0 * z 0 * g.inner p.1 v w := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let h := halfLineMetric.warpedProduct g (halfLineExp κ) (halfLineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * halfLineDepth q))
  let Φ := Diffeomorph.prodComm I (𝓡∂ 1) M (EuclideanHalfSpace 1) ∞
  have heq : g.exponentialWarpedEnd κ = Diffeomorph.pullbackMetricCross h Φ := rfl
  have hd : mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I)
      (Prod.swap : M × EuclideanHalfSpace 1 → EuclideanHalfSpace 1 × M) p =
      (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 1))).prod
        (ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin 1))) := by
    exact (mfderiv_prodMk mdifferentiableAt_snd mdifferentiableAt_fst).trans
      (by rw [mfderiv_snd, mfderiv_fst]; rfl)
  have ht := metricRm04Standard_pullbackCross h Φ p (0, u) (v, 0) (w, 0) (0, z)
  change metricRm04StandardAt (Diffeomorph.pullbackMetricCross h Φ) p
      (0, u) (v, 0) (w, 0) (0, z) =
    metricRm04StandardAt h (p.2, p.1)
      (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p (0, u))
      (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p (v, 0))
      (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p (w, 0))
      (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p (0, z)) at ht
  erw [hd] at ht
  change metricRm04StandardAt (Diffeomorph.pullbackMetricCross h Φ) p
      (0, u) (v, 0) (w, 0) (0, z) =
    metricRm04StandardAt h (p.2, p.1) (u, 0) (0, v) (0, w) (z, 0) at ht
  rw [heq]
  exact ht.trans (halfLineExp_mixed_curvature g κ (p.2, p.1) u z v w)


private theorem sectional_split {S : Type*} [AddCommGroup S] [Module ℝ S]
    {R : S → S → S → S → ℝ} (hR : IsAlgCurvForm R)
    (e U V : S) (a b : ℝ)
    (hUVU : R U V U e = 0) (hUVV : R U V V e = 0) :
    R (a • e + U) (b • e + V) (b • e + V) (a • e + U) =
      a ^ 2 * R e V V e - 2 * a * b * R e U V e +
        b ^ 2 * R e U U e + R U V V U := by
  have hs₂ (c : ℝ) (x y z w : S) : R x (c • y) z w = c * R x y z w := by
    rw [hR.anti_first, hR.smul_left, hR.anti_first y x]
    ring
  have hs₃ (c : ℝ) (x y z w : S) : R x y (c • z) w = c * R x y z w := by
    rw [hR.pair_swap, hR.smul_left, hR.pair_swap z w]
  have hs₄ (c : ℝ) (x y z w : S) : R x y z (c • w) = c * R x y z w := by
    rw [hR.anti_last, hs₃, hR.anti_last x y w]
    ring
  have hfirst (x y z : S) : R x x y z = 0 := by
    have hh := hR.anti_first x x y z
    linarith
  have hlast (x y z : S) : R x y z z = 0 := by
    have hh := hR.anti_last x y z z
    linarith
  have hmix : R e V U e = R e U V e := by
    have hh := hR.bianchi e V U e
    have hh' := hR.anti_first U e V e
    rw [hlast] at hh
    linarith
  have h₁ : R e V V U = 0 := by rw [hR.pair_swap, hR.anti_first, hR.anti_last, hUVV]; ring
  have h₂ : R U e V U = 0 := by rw [hR.pair_swap, hR.anti_first, hUVU]; ring
  have h₃ : R U V e U = 0 := by rw [hR.anti_last, hUVU]; ring
  have h₄ : R e V e U = -R e U V e := by rw [hR.anti_last, hmix]
  have h₅ : R U e V e = -R e U V e := hR.anti_first _ _ _ _
  have h₆ : R U e e U = R e U U e := by rw [hR.anti_first, hR.anti_last e U]; ring
  simp only [hR.add_left, hR.add_two, hR.add_three, hR.add_four,
    hR.smul_left, hs₂, hs₃, hs₄, hfirst, hlast,
    hUVV, h₁, h₂, h₃, h₄, h₅, h₆]
  ring

private theorem sectional_zero_four {S : Type*} [AddCommGroup S] [Module ℝ S]
    {R : S → S → S → S → ℝ} (hR : IsAlgCurvForm R) (a b c : S) :
    R a b c 0 = 0 := by
  have hz : R 0 c a b = 0 := by
    simpa only [zero_smul, zero_mul] using hR.smul_left 0 c c a b
  rw [hR.pair_swap, hR.anti_first, hz, neg_zero]

private theorem halfLineExp_square (κ : ℝ) (p : EuclideanHalfSpace 1) :
    halfLineExp κ p ^ 2 = Real.exp (-2 * κ * p.val 0) := by
  change Real.exp (-κ * p.val 0) ^ 2 = Real.exp (-2 * κ * p.val 0)
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem halfLineExp_grad_norm (κ : ℝ) (p : EuclideanHalfSpace 1) :
    halfLineMetric.inner p (gradFun halfLineMetric (halfLineExp κ) p)
      (gradFun halfLineMetric (halfLineExp κ) p) =
      κ ^ 2 * Real.exp (-2 * κ * p.val 0) := by
  erw [halfLineExp_grad, halfLineMetric_inner]
  change ((-κ * halfLineExp κ p) * 1) * ((-κ * halfLineExp κ p) * 1) = _
  rw [← halfLineExp_square κ p]
  ring

private theorem exponential_sectional_scalar (κ t a b A B C Q : ℝ) :
    a ^ 2 * (-κ ^ 2 * t * B) - 2 * a * b * (-κ ^ 2 * t * C) +
      b ^ 2 * (-κ ^ 2 * t * A) + t * (Q - κ ^ 2 * t * (A * B - C ^ 2)) =
      t * Q - κ ^ 2 * ((a * a + t * A) * (b * b + t * B) -
        (a * b + t * C) ^ 2) := by ring


variable {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

private abbrev halfLineWarped (h : SmoothRiemannianMetric J N) (κ : ℝ) :=
  halfLineMetric.warpedProduct h (halfLineExp κ) (halfLineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * halfLineDepth q))

private theorem halfLineWarped_triple (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanHalfSpace 1 × N) (a b c : F) :
    metricRm04StandardAt (halfLineWarped h κ) p
      (0, a) (0, b) (0, c) (halfLineUnit p.1, 0) = 0 := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let Rf : F → F → F → F → ℝ := metricRm04StandardAt h p.2
  have hRf : IsAlgCurvForm Rf :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule h p.2)
  have hh := metricRm04StandardAt_warpedProduct_vertical halfLineMetric h
    (halfLineExp κ) (halfLineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * halfLineDepth q)) p a b c 0 (halfLineUnit p.1)
  have ha : h.inner p.2 0 a = 0 := by rw [map_zero]; rfl
  have hb : h.inner p.2 0 b = 0 := by rw [map_zero]; rfl
  have hz : metricRm04StandardAt h p.2 a b c 0 = 0 := sectional_zero_four hRf a b c
  erw [hz, ha, hb] at hh
  erw [hh]
  ring

private theorem halfLineWarped_mixed (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanHalfSpace 1 × N) (a b : F) :
    metricRm04StandardAt (halfLineWarped h κ) p
      (halfLineUnit p.1, 0) (0, a) (0, b) (halfLineUnit p.1, 0) =
      -κ ^ 2 * Real.exp (-2 * κ * p.1.val 0) * h.inner p.2 a b := by
  have hh := halfLineExp_mixed_curvature h κ p (halfLineUnit p.1) (halfLineUnit p.1) a b
  change metricRm04StandardAt (halfLineWarped h κ) p
      (halfLineUnit p.1, 0) (0, a) (0, b) (halfLineUnit p.1, 0) =
      -κ ^ 2 * Real.exp (-2 * κ * p.1.val 0) * 1 * 1 * h.inner p.2 a b at hh
  simpa only [mul_one] using hh

private theorem halfLineWarped_vertical (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanHalfSpace 1 × N) (a b : F) :
    metricRm04StandardAt (halfLineWarped h κ) p (0, a) (0, b) (0, b) (0, a) =
      Real.exp (-2 * κ * p.1.val 0) * (metricRm04StandardAt h p.2 a b b a -
        κ ^ 2 * Real.exp (-2 * κ * p.1.val 0) *
          (h.inner p.2 a a * h.inner p.2 b b - h.inner p.2 a b ^ 2)) := by
  have hh := metricRm04StandardAt_warpedProduct_vertical halfLineMetric h
    (halfLineExp κ) (halfLineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * halfLineDepth q)) p a b b a 0
  rw [halfLineExp_square, halfLineExp_grad_norm] at hh
  exact hh.trans (by ring)

private theorem halfLineWarped_pair (h : SmoothRiemannianMetric J N) (κ : ℝ)
    (p : EuclideanHalfSpace 1 × N) (a b : EuclideanSpace ℝ (Fin 1) × F) :
    (halfLineWarped h κ).inner p a b = a.1 0 * b.1 0 +
      Real.exp (-2 * κ * p.1.val 0) * h.inner p.2 a.2 b.2 := by
  erw [SmoothRiemannianMetric.warpedProduct_inner, halfLineMetric_inner]
  rw [halfLineExp_square]

omit [FiniteDimensional ℝ F] in
private theorem halfLine_vector_split (p : EuclideanHalfSpace 1)
    (a : EuclideanSpace ℝ (Fin 1) × F) :
    a.1 0 • (halfLineUnit p, (0 : F)) + (0, a.2) = a := by
  apply Prod.ext
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    change a.1 0 * 1 + 0 = a.1 i
    rw [hi, mul_one, add_zero]
  · change a.1 0 • (0 : F) + a.2 = a.2
    rw [smul_zero, zero_add]

private theorem halfLineWarped_sectional_expansion
    (h : SmoothRiemannianMetric J N) (κ : ℝ) (p : EuclideanHalfSpace 1 × N)
    (v w : EuclideanSpace ℝ (Fin 1) × F) :
    metricRm04StandardAt (halfLineWarped h κ) p v w w v =
      (v.1 0) ^ 2 * (-κ ^ 2 * Real.exp (-2 * κ * p.1.val 0) * h.inner p.2 w.2 w.2) -
      2 * v.1 0 * w.1 0 * (-κ ^ 2 * Real.exp (-2 * κ * p.1.val 0) * h.inner p.2 v.2 w.2) +
      (w.1 0) ^ 2 * (-κ ^ 2 * Real.exp (-2 * κ * p.1.val 0) * h.inner p.2 v.2 v.2) +
      Real.exp (-2 * κ * p.1.val 0) * (metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2 -
        κ ^ 2 * Real.exp (-2 * κ * p.1.val 0) *
          (h.inner p.2 v.2 v.2 * h.inner p.2 w.2 w.2 - h.inner p.2 v.2 w.2 ^ 2)) := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let R : (EuclideanSpace ℝ (Fin 1) × F) → (EuclideanSpace ℝ (Fin 1) × F) →
      (EuclideanSpace ℝ (Fin 1) × F) → (EuclideanSpace ℝ (Fin 1) × F) → ℝ :=
    metricRm04StandardAt (halfLineWarped h κ) p
  have hR : IsAlgCurvForm R :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (halfLineWarped h κ) p)
  have hs := sectional_split hR (halfLineUnit p.1, (0 : F)) (0, v.2) (0, w.2)
    (v.1 0) (w.1 0) (halfLineWarped_triple h κ p v.2 w.2 v.2)
    (halfLineWarped_triple h κ p v.2 w.2 w.2)
  erw [halfLine_vector_split p.1 v, halfLine_vector_split p.1 w] at hs
  change R v w w v = _
  refine hs.trans ?_
  change (v.1 0) ^ 2 * metricRm04StandardAt (halfLineWarped h κ) p
      (halfLineUnit p.1, 0) (0, w.2) (0, w.2) (halfLineUnit p.1, 0) -
    2 * v.1 0 * w.1 0 * metricRm04StandardAt (halfLineWarped h κ) p
      (halfLineUnit p.1, 0) (0, v.2) (0, w.2) (halfLineUnit p.1, 0) +
    (w.1 0) ^ 2 * metricRm04StandardAt (halfLineWarped h κ) p
      (halfLineUnit p.1, 0) (0, v.2) (0, v.2) (halfLineUnit p.1, 0) +
    metricRm04StandardAt (halfLineWarped h κ) p (0, v.2) (0, w.2) (0, w.2) (0, v.2) = _
  rw [halfLineWarped_mixed, halfLineWarped_mixed, halfLineWarped_mixed, halfLineWarped_vertical]

private theorem halfLineExp_sectional
    (h : SmoothRiemannianMetric J N) (κ : ℝ) (p : EuclideanHalfSpace 1 × N)
    (v w : EuclideanSpace ℝ (Fin 1) × F) :
    let G := halfLineMetric.warpedProduct h (halfLineExp κ) (halfLineExp_smooth κ)
      (fun q => Real.exp_pos (-κ * halfLineDepth q))
    metricRm04StandardAt G p v w w v =
      Real.exp (-2 * κ * p.1.val 0) * metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2 -
      κ ^ 2 * (G.inner p v v * G.inner p w w - G.inner p v w ^ 2) := by
  change metricRm04StandardAt (halfLineWarped h κ) p v w w v = _
  rw [halfLineWarped_sectional_expansion]
  change _ = Real.exp (-2 * κ * p.1.val 0) * metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2 -
    κ ^ 2 * ((halfLineWarped h κ).inner p v v * (halfLineWarped h κ).inner p w w -
      (halfLineWarped h κ).inner p v w ^ 2)
  rw [halfLineWarped_pair, halfLineWarped_pair, halfLineWarped_pair]
  exact exponential_sectional_scalar κ (Real.exp (-2 * κ * p.1.val 0))
    (v.1 0) (w.1 0) (h.inner p.2 v.2 v.2) (h.inner p.2 w.2 w.2)
    (h.inner p.2 v.2 w.2) (metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2)


theorem metricRm04StandardAt_exponentialWarpedEnd_sectional
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (κ : ℝ) (p : M × EuclideanHalfSpace 1)
    (v w : TangentSpace (I.prod (𝓡∂ 1)) p) :
    metricRm04StandardAt (g.exponentialWarpedEnd κ) p v w w v =
      Real.exp (-2 * κ * p.2.val 0) * metricRm04StandardAt g p.1 v.1 w.1 w.1 v.1 -
      κ ^ 2 * ((g.exponentialWarpedEnd κ).inner p v v *
        (g.exponentialWarpedEnd κ).inner p w w - (g.exponentialWarpedEnd κ).inner p v w ^ 2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let G := halfLineMetric.warpedProduct g (halfLineExp κ) (halfLineExp_smooth κ)
    (fun q => Real.exp_pos (-κ * halfLineDepth q))
  let Φ := Diffeomorph.prodComm I (𝓡∂ 1) M (EuclideanHalfSpace 1) ∞
  have heq : g.exponentialWarpedEnd κ = Diffeomorph.pullbackMetricCross G Φ := rfl
  have hd : mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I)
      (Prod.swap : M × EuclideanHalfSpace 1 → EuclideanHalfSpace 1 × M) p =
      (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 1))).prod
        (ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin 1))) := by
    exact (mfderiv_prodMk mdifferentiableAt_snd mdifferentiableAt_fst).trans
      (by rw [mfderiv_snd, mfderiv_fst]; rfl)
  have ht := metricRm04Standard_pullbackCross G Φ p v w w v
  change metricRm04StandardAt (Diffeomorph.pullbackMetricCross G Φ) p v w w v =
    metricRm04StandardAt G (p.2, p.1)
      (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p v)
      (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p w)
      (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p w)
      (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p v) at ht
  erw [hd] at ht
  change metricRm04StandardAt (Diffeomorph.pullbackMetricCross G Φ) p v w w v =
    metricRm04StandardAt G (p.2, p.1) (v.2, v.1) (w.2, w.1) (w.2, w.1) (v.2, v.1) at ht
  have hG (a b : TangentSpace (I.prod (𝓡∂ 1)) p) :
      G.inner (p.2, p.1) (a.2, a.1) (b.2, b.1) =
      (g.exponentialWarpedEnd κ).inner p a b := by
    have hi := Diffeomorph.pullbackMetricCross_inner G Φ p a b
    change (Diffeomorph.pullbackMetricCross G Φ).inner p a b =
      G.inner (p.2, p.1)
        (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p a)
        (mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) Prod.swap p b) at hi
    erw [hd] at hi
    exact hi.symm
  have hb := halfLineExp_sectional g κ (p.2, p.1) (v.2, v.1) (w.2, w.1)
  change metricRm04StandardAt G (p.2, p.1) (v.2, v.1) (w.2, w.1) (w.2, w.1) (v.2, v.1) = _ at hb
  rw [hG v v, hG w w, hG v w] at hb
  rw [← heq] at ht
  exact ht.trans hb

end DifferentialGeometry.Geometry.Curvature
