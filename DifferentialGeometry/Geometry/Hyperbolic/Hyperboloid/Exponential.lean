import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Curvature
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Agreement
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.CurvatureBound
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Inverse
import Mathlib.Analysis.SpecialFunctions.Arsinh
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianDistance
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

noncomputable section

open scoped _root_.Manifold ContDiff Bundle

namespace DifferentialGeometry.Hyperboloid

open Geometry.Riemannian (IsMetricNorm isMetricNorm_of_riemannianBundle)
open Geometry.Riemannian.Exponential (intrinsicGeodesic intrinsicGeodesic_isGeodesic
  intrinsicGeodesic_zero intrinsicGeodesic_mfderiv_zero intrinsicGeodesic_continuous
  isGeodesic_eq_of_initial expMapIntrinsic expMapIntrinsic_def)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem isRiemannianManifold_riemannianMetric :
    letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
    IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) := by
  let _ : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
  exact ⟨fun x y => (riemannianEDistOf_eq_edist x y).symm⟩

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicGeodesic_origin (u : E) (t : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
    letI : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
      isRiemannianManifold_riemannianMetric
    letI : IsContinuousRiemannianBundle E
        (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      (isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))).isContinuousRiemannianBundle
    intrinsicGeodesic (I := 𝓘(ℝ, E)) riemannianMetric
      (isMetricNorm_of_riemannianBundle riemannianMetric) origin (spaceVectorField u origin) t =
      ofSpace ((Real.sinh (t * ‖u‖) / ‖u‖) • u) := by
  let _ : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
    isRiemannianManifold_riemannianMetric
  let _ : IsContinuousRiemannianBundle E
      (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    (isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))).isContinuousRiemannianBundle
  let hnorm := isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))
  let γ := intrinsicGeodesic (I := 𝓘(ℝ, E)) riemannianMetric hnorm
    origin (spaceVectorField u origin)
  change γ t = _
  have hγgeo := intrinsicGeodesic_isGeodesic riemannianMetric hnorm
    origin (spaceVectorField u origin)
  have hγcont := intrinsicGeodesic_continuous riemannianMetric hnorm
    origin (spaceVectorField u origin)
  have hγ0 := intrinsicGeodesic_zero riemannianMetric hnorm
    origin (spaceVectorField u origin)
  have hγv := intrinsicGeodesic_mfderiv_zero riemannianMetric hnorm
    origin (spaceVectorField u origin)
  by_cases hu : u = 0
  · have heq : γ = fun _ => (origin : Hyperboloid E) := by
      apply isGeodesic_eq_of_initial riemannianMetric hγgeo
        (Geometry.Riemannian.Geodesic.isGeodesic_const riemannianMetric origin)
        hγcont continuous_const hγ0
      rw [hγv, hu, mfderiv_const]
      rfl
    rw [heq, hu]
    simp only [smul_zero]
    rfl
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  let w : E := ‖u‖⁻¹ • u
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u)]
    exact inv_mul_cancel₀ hn
  have hv : lorentzForm E (0, w) (0, w) = 1 := by
    simp only [lorentzForm_apply, real_inner_self_eq_norm_sq, hw]
    norm_num
  have ho : lorentzForm E ((origin : Hyperboloid E).time, (origin : Hyperboloid E).space)
      (0, w) = 0 := by simp
  let c := geodesicLine (origin : Hyperboloid E) (0, w) hv ho
  let η : ℝ → Hyperboloid E := fun s => c (‖u‖ * s)
  have hηgeo : Geometry.Riemannian.Geodesic.IsGeodesic (I := 𝓘(ℝ, E)) riemannianMetric η := by
    intro s
    simpa only [add_zero] using
      Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_comp_affine
        (g := riemannianMetric) (c := ‖u‖) (d := 0) (t := s)
        (isGeodesic_geodesicLine origin (0, w) hv ho (‖u‖ * s + 0))
  have hηcont : Continuous η :=
    (contMDiff_geodesicLine (n := ∞) origin (0, w) hv ho).continuous.comp
      (continuous_const.mul continuous_id)
  have hη0 : η 0 = origin := by
    simp only [η, c, mul_zero, geodesicLine_zero]
  have hηv : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η 0 (1 : ℝ) : E) = u := by
    have hd := (contMDiff_geodesicLine (n := ∞) origin (0, w) hv ho).mdifferentiableAt
      (x := (0 : ℝ)) (by simp)
    have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => ‖u‖ * s) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul ‖u‖).differentiableAt.mdifferentiableAt
    have hv0 := mfderiv_space_geodesicLine_apply_one origin (0, w) hv ho 0
    rw [mfderiv_spaceDiffeomorph] at hv0
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1 : E) =
      Real.sinh 0 • (origin : Hyperboloid E).space + Real.cosh 0 • w at hv0
    have hv0' : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1 : E) = w := by
      simpa only [Real.sinh_zero, Real.cosh_zero, zero_smul, one_smul, zero_add] using hv0
    have hd' : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (‖u‖ * 0) := by
      simpa only [mul_zero] using hd
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (c ∘ fun s : ℝ => ‖u‖ * s) 0 1 : E) = u
    rw [mfderiv_comp_apply 0 hd' hs]
    have hscale : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => ‖u‖ * s) 0 1 = ‖u‖ := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun s : ℝ => ‖u‖ * s) 0 1 = ‖u‖
      rw [fderiv_apply_one_eq_deriv]
      simpa only [mul_one, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_mul ‖u‖).deriv
    rw [hscale, mul_zero]
    let A : ℝ →L[ℝ] E := tangentLinearMapToModel (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0)
    have hA : A 1 = w := hv0'
    change A ‖u‖ = u
    calc
      A ‖u‖ = ‖u‖ • A 1 := by simpa only [smul_eq_mul, mul_one] using map_smul A ‖u‖ (1 : ℝ)
      _ = u := by rw [hA]; simp only [w, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have heq : γ = η := isGeodesic_eq_of_initial riemannianMetric hγgeo hηgeo
    hγcont hηcont (hγ0.trans hη0.symm) (hγv.trans hηv.symm)
  rw [heq]
  apply ext
  change Real.cosh (‖u‖ * t) • (origin : Hyperboloid E).space +
    Real.sinh (‖u‖ * t) • w = (Real.sinh (t * ‖u‖) / ‖u‖) • u
  rw [origin_space, smul_zero, zero_add]
  simp only [w, smul_smul, div_eq_mul_inv, mul_comm ‖u‖ t]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expMapIntrinsic_origin (u : E) :
    letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
    letI : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
      isRiemannianManifold_riemannianMetric
    letI : IsContinuousRiemannianBundle E
        (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      (isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))).isContinuousRiemannianBundle
    expMapIntrinsic (I := 𝓘(ℝ, E)) riemannianMetric
      (isMetricNorm_of_riemannianBundle riemannianMetric) origin (spaceVectorField u origin) =
      ofSpace ((Real.sinh ‖u‖ / ‖u‖) • u) := by
  simpa only [expMapIntrinsic_def, one_mul] using intrinsicGeodesic_origin u 1

end DifferentialGeometry.Hyperboloid

namespace DifferentialGeometry.Hyperboloid

open scoped Topology

section Radial

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_radial (f : ℝ → ℝ) (hf : f 0 = 0) (u : F) :
    ‖(f ‖u‖ / ‖u‖) • u‖ = |f ‖u‖| := by
  by_cases hu : u = 0
  · simp only [hu, norm_zero, hf, div_zero, zero_smul, abs_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg u),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hu)]

private theorem continuous_radial (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    Continuous (fun u : F => (f ‖u‖ / ‖u‖) • u) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u = 0
  · subst u
    change Filter.Tendsto (fun u : F => (f ‖u‖ / ‖u‖) • u) (𝓝 0)
      (𝓝 ((f ‖(0 : F)‖ / ‖(0 : F)‖) • (0 : F)))
    rw [smul_zero]
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h := (hf.comp (continuous_norm : Continuous (norm : F → ℝ))).abs.tendsto (0 : F)
    simpa only [Function.comp_def, dist_zero_right, norm_radial f hf0, norm_zero, hf0, abs_zero] using h
  · exact ((hf.continuousAt.comp continuous_norm.continuousAt).div
      continuous_norm.continuousAt (norm_ne_zero_iff.mpr hu)).smul continuous_id.continuousAt

private theorem radial_inverse (f g : ℝ → ℝ) (hf0 : f 0 = 0)
    (hfpos : ∀ r : ℝ, 0 < r → 0 < f r) (hgf : ∀ r : ℝ, g (f r) = r) (u : F) :
    (g ‖(f ‖u‖ / ‖u‖) • u‖ / ‖(f ‖u‖ / ‖u‖) • u‖) • ((f ‖u‖ / ‖u‖) • u) = u := by
  by_cases hu : u = 0
  · simp only [hu, smul_zero]
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hfr := hfpos ‖u‖ hr
  rw [norm_radial f hf0, abs_of_pos hfr, hgf, smul_smul]
  have hcancel : (‖u‖ / f ‖u‖) * (f ‖u‖ / ‖u‖) = 1 := by
    field_simp [hr.ne', hfr.ne']
  rw [hcancel, one_smul]

end Radial

open Geometry.Riemannian (isMetricNorm_of_riemannianBundle)
open Geometry.Riemannian.Exponential (expMapIntrinsic)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def expMapIntrinsicOriginHomeomorph :
    letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
    letI : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
      isRiemannianManifold_riemannianMetric
    letI : IsContinuousRiemannianBundle E
        (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      (isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))).isContinuousRiemannianBundle
    E ≃ₜ Hyperboloid E := by
  let _ : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
    isRiemannianManifold_riemannianMetric
  let _ : IsContinuousRiemannianBundle E
      (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    (isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))).isContinuousRiemannianBundle
  refine
    { toFun := fun u => expMapIntrinsic (I := 𝓘(ℝ, E)) riemannianMetric
        (isMetricNorm_of_riemannianBundle riemannianMetric) origin (spaceVectorField u origin)
      invFun := fun x => (Real.arsinh ‖x.space‖ / ‖x.space‖) • x.space
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro u
    dsimp only
    rw [expMapIntrinsic_origin, space_ofSpace]
    exact radial_inverse Real.sinh Real.arsinh Real.sinh_zero
      (fun _ hr => Real.sinh_pos_iff.mpr hr) Real.arsinh_sinh u
  · intro x
    dsimp only
    rw [expMapIntrinsic_origin]
    apply ext
    rw [space_ofSpace]
    exact radial_inverse Real.arsinh Real.sinh Real.arsinh_zero
      (fun _ hr => Real.arsinh_pos_iff.mpr hr) Real.sinh_arsinh x.space
  · have heq : (fun u : E => expMapIntrinsic (I := 𝓘(ℝ, E)) riemannianMetric
        (isMetricNorm_of_riemannianBundle riemannianMetric) origin (spaceVectorField u origin)) =
        fun u => ofSpace ((Real.sinh ‖u‖ / ‖u‖) • u) := funext expMapIntrinsic_origin
    rw [heq]
    exact continuous_ofSpace.comp (continuous_radial Real.sinh Real.continuous_sinh Real.sinh_zero)
  · exact (continuous_radial Real.arsinh Real.continuous_arsinh Real.arsinh_zero).comp continuous_space

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
@[simp] theorem expMapIntrinsicOriginHomeomorph_apply (u : E) :
    letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
    letI : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
      isRiemannianManifold_riemannianMetric
    letI : IsContinuousRiemannianBundle E
        (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
      (isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))).isContinuousRiemannianBundle
    expMapIntrinsicOriginHomeomorph u = expMapIntrinsic (I := 𝓘(ℝ, E)) riemannianMetric
      (isMetricNorm_of_riemannianBundle riemannianMetric) origin (spaceVectorField u origin) := rfl

@[simp] theorem expMapIntrinsicOriginHomeomorph_symm_apply (x : Hyperboloid E) :
    expMapIntrinsicOriginHomeomorph.symm x = (Real.arsinh ‖x.space‖ / ‖x.space‖) • x.space := rfl

end DifferentialGeometry.Hyperboloid

namespace DifferentialGeometry.Hyperboloid

open Geometry.Riemannian (isMetricNorm_of_riemannianBundle)
open Geometry.Riemannian.Exponential (expMap expDomain expDomain_eq_univ_of_completeSpace
  expMap_eq_expMapIntrinsic contMDiffAt_expMap injective_mfderiv_expMap_of_curvature_upper_bound)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E)] in
private theorem inner_riemannOp_self_nonpos (x : Hyperboloid E)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    riemannianMetric.inner x
      (Geometry.Curvature.riemannOp (Geometry.Connection.LeviCivita riemannianMetric) x v w w) v ≤ 0 := by
  have hden := Geometry.Riemannian.sectionalCurvatureDenominator_nonneg riemannianMetric x v w
  rw [Geometry.Riemannian.sectionalCurvatureDenominator_def] at hden
  calc
    riemannianMetric.inner x
        (Geometry.Curvature.riemannOp (Geometry.Connection.LeviCivita riemannianMetric) x v w w) v =
        Geometry.Curvature.metricRm04StandardAt riemannianMetric x v w w v := by
      rw [Geometry.Curvature.rm04_eq_inner]
      exact riemannianMetric.symm x _ _
    _ ≤ 0 := by
      rw [metricRm04StandardAt_riemannianMetric, riemannianMetric.symm x w v]
      nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isLocalDiffeomorph_expMapIntrinsicOriginHomeomorph :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (expMapIntrinsicOriginHomeomorph (E := E) : E → Hyperboloid E) := by
  let _ : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    ⟨(riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
    isRiemannianManifold_riemannianMetric
  let _ : IsContinuousRiemannianBundle E
      (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    (isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))).isContinuousRiemannianBundle
  let hnorm := isMetricNorm_of_riemannianBundle (riemannianMetric (E := E))
  have heq : (expMapIntrinsicOriginHomeomorph (E := E) : E → Hyperboloid E) =
      fun u : E => expMap (I := 𝓘(ℝ, E)) riemannianMetric origin
        (show TangentSpace 𝓘(ℝ, E) (origin : Hyperboloid E) from u) := by
    funext u
    rw [expMapIntrinsicOriginHomeomorph_apply, expMap_eq_expMapIntrinsic riemannianMetric hnorm]
    rfl
  rw [heq]
  apply isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ.mpr
  have hdom (u : E) : (show TangentSpace 𝓘(ℝ, E) (origin : Hyperboloid E) from u) ∈
      expDomain (I := 𝓘(ℝ, E)) riemannianMetric origin := by
    rw [expDomain_eq_univ_of_completeSpace riemannianMetric hnorm]
    trivial
  have hs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun u : E => expMap (I := 𝓘(ℝ, E)) riemannianMetric origin
        (show TangentSpace 𝓘(ℝ, E) (origin : Hyperboloid E) from u)) Set.univ :=
    fun u _ => (contMDiffAt_expMap riemannianMetric origin (hdom u)).contMDiffWithinAt
  apply hs.isLocalDiffeomorphOn_of_isInvertible_mfderiv isOpen_univ (by simp)
  intro u _
  have hi := injective_mfderiv_expMap_of_curvature_upper_bound
    riemannianMetric (origin : Hyperboloid E) u (hdom u)
    (κ := 0) (by positivity) (by
      intro t _ v
      simp only [zero_mul]
      exact inner_riemannOp_self_nonpos _ v _)
  have hsurj := LinearMap.surjective_of_injective hi
  let D : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun w : E => expMap (I := 𝓘(ℝ, E)) riemannianMetric origin
        (show TangentSpace 𝓘(ℝ, E) (origin : Hyperboloid E) from w)) u)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨D, rfl⟩

def expMapIntrinsicOriginDiffeomorph : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ Hyperboloid E where
  toEquiv := expMapIntrinsicOriginHomeomorph.toEquiv
  contMDiff_toFun := isLocalDiffeomorph_expMapIntrinsicOriginHomeomorph.contMDiff
  contMDiff_invFun := by
    intro x
    exact ((expMapIntrinsicOriginHomeomorph (E := E)).isLocalDiffeomorphAt_symm_iff.mpr
      (isLocalDiffeomorph_expMapIntrinsicOriginHomeomorph
        (expMapIntrinsicOriginHomeomorph.symm x))).contMDiffAt

@[simp] theorem expMapIntrinsicOriginDiffeomorph_toHomeomorph :
    (expMapIntrinsicOriginDiffeomorph (E := E)).toHomeomorph = expMapIntrinsicOriginHomeomorph := rfl

@[simp] theorem expMapIntrinsicOriginDiffeomorph_apply (u : E) :
    expMapIntrinsicOriginDiffeomorph u = expMapIntrinsicOriginHomeomorph u := rfl

@[simp] theorem expMapIntrinsicOriginDiffeomorph_symm_apply (x : Hyperboloid E) :
    expMapIntrinsicOriginDiffeomorph.symm x = (Real.arsinh ‖x.space‖ / ‖x.space‖) • x.space := rfl

end DifferentialGeometry.Hyperboloid
