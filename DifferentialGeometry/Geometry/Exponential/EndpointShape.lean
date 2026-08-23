import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Geometry.Exponential.BranchRadius
import DifferentialGeometry.Geometry.Exponential.IntrinsicGauss
import DifferentialGeometry.Geometry.Exponential.JacobiVariation
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Integral.DivergenceTheorem


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

private theorem curveVelocity_comp_mul
    (γ : Real → M) (c t : Real)
    (hγ : MDifferentiableAt 𝓘(Real, Real) I γ (c * t)) :
    curveVelocity (I := I) (fun s => γ (c * s)) t =
      c • curveVelocity (I := I) γ (c * t) := by
  let a : Real → Real := fun s => c * s
  have ha : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real) a t := by
    have haInf : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ a :=
      contMDiff_const.mul contMDiff_id
    exact haInf.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_apply (f := a) (g := γ) (x := t)
    hγ ha (1 : Real)
  have ha_one :
      mfderiv 𝓘(Real, Real) 𝓘(Real, Real) a t (1 : Real) = c := by
    rw [mfderiv_eq_fderiv]
    have hfd : HasFDerivAt a (c • (1 : Real →L[Real] Real)) t := by
      simpa only [a] using (hasFDerivAt_id t).const_mul c
    rw [hfd.fderiv]
    change c * 1 = c
    ring
  change mfderiv 𝓘(Real, Real) I (γ ∘ a) t (1 : Real) =
    c • mfderiv 𝓘(Real, Real) I γ (a t) (1 : Real)
  rw [hcomp, ha_one]
  simpa only [smul_eq_mul, mul_one] using
    map_smul (mfderiv 𝓘(Real, Real) I γ (a t)) c (1 : Real)


variable [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable [I.Boundaryless]
variable [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable def intrinsicJacobi
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : TangentSpace I p) (s : Real) :
    TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p u s) :=
  mfderiv 𝓘(Real, Real) I
    (fun r : Real =>
      intrinsicGeodesic (I := I) g hEnorm p (u + r • w) s)
    0 1

@[simp] theorem intrinsicJacobi_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w : TangentSpace I p) :
    intrinsicJacobi (I := I) g hEnorm p u w 0 = 0 := by
  have hconst :
      (fun r : Real =>
        intrinsicGeodesic (I := I) g hEnorm p (u + r • w) 0) =
        fun _ : Real => p := by
    funext r
    exact intrinsicGeodesic_zero (I := I) g hEnorm p _
  unfold intrinsicJacobi
  rw [hconst, mfderiv_const]
  rfl

theorem intrJacobi_diff
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w : TangentSpace I p) (t : Real) :
    DifferentiableAt Real
        (chartRepAt (I := I)
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (intrinsicJacobi (I := I) g hEnorm p u w) t) t ∧
      DifferentiableAt Real
        (chartRepAt (I := I)
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun s => covDerivAlong (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (intrinsicJacobi (I := I) g hEnorm p u w) s) t) t := by
  let F : Real → Real → M := fun s r =>
    intrinsicGeodesic (I := I) g hEnorm p (u + s • w) r
  have hF : IsSmoothVariation (I := I) F := by
    change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
      (fun q : Real × Real =>
        intrinsicGeodesic (I := I) g hEnorm p (u + q.1 • w) q.2)
    exact (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (w : E)).of_le
      ENat.LEInfty.out
  have hbase :
      (fun r : Real => F 0 r) =
        intrinsicGeodesic (I := I) g hEnorm p u := by
    funext r
    simp only [F, zero_smul, add_zero]
  have hfield :
      (fun r : Real =>
        mfderiv 𝓘(Real, Real) I (fun s : Real => F s r) 0 (1 : Real)) =
        intrinsicJacobi (I := I) g hEnorm p u w := by
    funext r
    rfl
  constructor
  · have h :=
      variationField_chartRep_differentiableAt (I := I) F hF t
    rw [hbase, hfield] at h
    exact h
  · have h :=
      variationField_covDeriv_chartRep_differentiableAt (I := I) g F hF t
    rw [hbase, hfield] at h
    exact h

theorem intrinsicJacobi_perp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u w : TangentSpace I p) :
    g.inner
        (intrinsicGeodesic (I := I) g hEnorm p u 1)
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd
        (intrinsicJacobi (I := I) g hEnorm p u w 1)
      = g.inner p u w := by
  have hgauss :=
    intrinsic_gauss (I := I) g hEnorm p (u : E) (w : E)
  have hjac :=
    intrinsic_jacobi_one (I := I) g hEnorm p (u : E) (w : E)
  rw [← hjac] at hgauss
  simpa only [intrinsicJacobi, expMapIntrinsic_def] using hgauss


private theorem intrVel_smul
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u : TangentSpace I p) (c : Real) :
    ((intrinsicVelocityLift (I := I) g hEnorm p (c • u) 1).snd : E) =
      c • ((intrinsicVelocityLift (I := I) g hEnorm p u c).snd : E) := by
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hfun :
      (fun s : Real =>
        intrinsicGeodesic (I := I) g hEnorm p (c • u) s) =
        fun s => γ (c * s) := by
    funext s
    calc
      intrinsicGeodesic (I := I) g hEnorm p (c • u) s =
          intrinsicGeodesic (I := I) g hEnorm p (s • (c • u)) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm p (c • u) s).symm
      _ = intrinsicGeodesic (I := I) g hEnorm p ((c * s) • u) 1 := by
        rw [smul_smul, mul_comm]
      _ = γ (c * s) := by
        simpa only [γ] using
          intrinsicGeodesic_smul (I := I) g hEnorm p u (c * s)
  have hγ :
      MDifferentiableAt 𝓘(Real, Real) I γ (c * 1) :=
    ((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p u).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by norm_num)
  have hvel := curveVelocity_comp_mul (I := I) γ c 1 hγ
  change
    (curveVelocity (I := I)
      (fun s => intrinsicGeodesic (I := I) g hEnorm p (c • u) s) 1 : E) =
      c • (curveVelocity (I := I) γ c : E)
  rw [hfun]
  have hct : c * 1 = c := mul_one c
  rw [hct] at hvel
  exact hvel

theorem intrJacobi_perp_ne
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w : TangentSpace I p) {t : Real}
    (ht : t ≠ 0) (hperp : g.inner p u w = 0) :
    g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
        (curveVelocity (I := I)
          (intrinsicGeodesic (I := I) g hEnorm p u) t)
        (intrinsicJacobi (I := I) g hEnorm p u w t) = 0 := by
  have hfield :
      (intrinsicJacobi (I := I) g hEnorm p u w t : E) =
        (intrinsicJacobi (I := I) g hEnorm p (t • u) (t • w) 1 : E) := by
    have hleft :
        (intrinsicJacobi (I := I) g hEnorm p u w t : E) =
          mfderiv 𝓘(Real, E) I
            (fun z : E => expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from z))
            (t • (u : E)) (t • (w : E)) :=
      intrinsic_jacobi_at (I := I) g hEnorm p (u : E) (w : E) t
    have hright :
        (intrinsicJacobi (I := I) g hEnorm p (t • u) (t • w) 1 : E) =
          mfderiv 𝓘(Real, E) I
            (fun z : E => expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from z))
            (t • (u : E)) (t • (w : E)) := by
      change
        mfderiv 𝓘(Real, Real) I
            (fun s : Real =>
              intrinsicGeodesic (I := I) g hEnorm p
                (show TangentSpace I p from
                  t • (u : E) + s • (t • (w : E))) 1)
            0 (1 : Real) =
          mfderiv 𝓘(Real, E) I
            (fun z : E => expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from z))
            (t • (u : E)) (t • (w : E))
      exact intrinsic_jacobi_one (I := I) g hEnorm p
        (t • (u : E)) (t • (w : E))
    exact hleft.trans hright.symm
  have hscaled :=
    intrinsicJacobi_perp (I := I) g hEnorm p (t • u) (t • w)
  rw [intrinsicGeodesic_smul (I := I) g hEnorm p u t,
    intrVel_smul (I := I) g hEnorm p u t, ← hfield] at hscaled
  have hright : g.inner p (t • u) (t • w) = 0 := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      hperp, mul_zero]
  rw [hright] at hscaled
  change
    g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
        (t • curveVelocity (I := I)
          (intrinsicGeodesic (I := I) g hEnorm p u) t)
        (intrinsicJacobi (I := I) g hEnorm p u w t) = 0 at hscaled
  have hmul :
      t * g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (intrinsicJacobi (I := I) g hEnorm p u w t) = 0 := by
    simpa only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] using
      hscaled
  exact (mul_eq_zero.mp hmul).resolve_left ht

theorem intrJacobi_self
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u : TangentSpace I p) :
    intrinsicJacobi (I := I) g hEnorm p u u 1 =
      curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p u) 1 := by
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hrepar :
      (fun r : Real =>
        intrinsicGeodesic (I := I) g hEnorm p (u + r • u) 1) =
        fun r : Real => γ (1 + r) := by
    funext r
    have hsmul : u + r • u = (1 + r) • u := by
      rw [add_smul, one_smul]
    rw [hsmul, intrinsicGeodesic_smul
      (I := I) g hEnorm p u (1 + r)]
  have hγdiff : MDifferentiableAt 𝓘(Real, Real) I γ 1 :=
    ((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p u).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by norm_num)
  have hshift :
      HasMFDerivAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun r : Real => 1 + r) 0 (ContinuousLinearMap.id Real Real) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    simpa using ((hasFDerivAt_id (0 : Real)).const_add (1 : Real))
  have hγat :
      HasMFDerivAt 𝓘(Real, Real) I γ (1 + (0 : Real))
        (mfderiv 𝓘(Real, Real) I γ 1) := by
    rw [add_zero]
    exact hγdiff.hasMFDerivAt
  have hcomp :
      HasMFDerivAt 𝓘(Real, Real) I
        (fun r : Real => γ (1 + r)) 0
        ((mfderiv 𝓘(Real, Real) I γ 1).comp
          (ContinuousLinearMap.id Real Real)) :=
    hγat.comp 0 hshift
  have hJ :
      HasMFDerivAt 𝓘(Real, Real) I
        (fun r : Real =>
          intrinsicGeodesic (I := I) g hEnorm p (u + r • u) 1) 0
        ((mfderiv 𝓘(Real, Real) I γ 1).comp
          (ContinuousLinearMap.id Real Real)) := by
    rw [hrepar]
    exact hcomp
  change
    mfderiv 𝓘(Real, Real) I
        (fun r : Real =>
          intrinsicGeodesic (I := I) g hEnorm p (u + r • u) 1)
        0 1 = mfderiv 𝓘(Real, Real) I γ 1 1
  rw [hJ.mfderiv]
  rfl

private theorem intrGeodesic_smooth
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u : TangentSpace I p) :
    ContMDiff 𝓘(Real, Real) I (8 : Nat)
      (intrinsicGeodesic (I := I) g hEnorm p u) := by
  let F : Real → Real → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p (u + s • (0 : TangentSpace I p)) t
  have hF : IsSmoothVariation (I := I) F := by
    change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
      (fun q : Real × Real =>
        intrinsicGeodesic (I := I) g hEnorm p
          (u + q.1 • (0 : TangentSpace I p)) q.2)
    exact (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (0 : E)).of_le
      ENat.LEInfty.out
  have hincl : ContMDiff 𝓘(Real, Real)
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
      (fun t : Real => ((0 : Real), t)) :=
    contMDiff_const.prodMk contMDiff_id
  have hcomp := (hF : ContMDiff _ _ _ _).comp hincl
  have heq :
      ((fun q : Real × Real => F q.1 q.2) ∘
          fun t : Real => ((0 : Real), t)) =
        intrinsicGeodesic (I := I) g hEnorm p u := by
    funext t
    simp only [F, Function.comp_apply, zero_smul, add_zero]
  rw [heq] at hcomp
  exact hcomp

theorem intrJacobi_dperp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w : TangentSpace I p) {t : Real}
    (ht : t ≠ 0) (hperp : g.inner p u w = 0) :
    g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
      (curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p u) t)
      (covDerivAlong (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (intrinsicJacobi (I := I) g hEnorm p u w) t) = 0 := by
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let J := intrinsicJacobi (I := I) g hEnorm p u w
  have hγInf : ContMDiff 𝓘(Real, Real) I (8 : Nat) γ :=
    intrGeodesic_smooth (I := I) g hEnorm p u
  have hγ : ContMDiffAt 𝓘(Real, Real) I 2 γ t :=
    hγInf.contMDiffAt.of_le (by norm_num)
  have hgeo : HasGeodesicEquationAt (I := I) g γ t := by
    simpa only [γ] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u t
  have hvelDiff : DifferentiableAt Real
      (chartRepAt (I := I) γ (curveVelocity (I := I) γ) t) t := by
    simpa only [curveVelocity, chartRepAt] using
      MFDerivAlongCurve.velocity_coord_diff (I := I) γ t hγ
  have hJdiff : DifferentiableAt Real
      (chartRepAt (I := I) γ J t) t := by
    simpa only [γ, J] using
      (intrJacobi_diff (I := I) g hEnorm p u w t).1
  have hinner := inner_deriv_at (I := I) (n := (2 : WithTop ℕ∞))
    (by norm_num) g γ (curveVelocity (I := I) γ) J t hγ hvelDiff hJdiff
  have hne : ∀ᶠ s in 𝓝 t, s ≠ 0 := eventually_ne_nhds ht
  have hzeroEv :
      (fun s : Real =>
        g.inner (γ s) (curveVelocity (I := I) γ s) (J s)) =ᶠ[𝓝 t]
        (fun _ : Real => 0) := by
    filter_upwards [hne] with s hs
    simpa only [γ, J] using
      intrJacobi_perp_ne (I := I) g hEnorm p u w hs hperp
  have hzero : HasDerivAt
      (fun s : Real =>
        g.inner (γ s) (curveVelocity (I := I) γ s) (J s)) 0 t :=
    (hasDerivAt_const (x := t) (c := (0 : Real))).congr_of_eventuallyEq hzeroEv
  have hvelZero :
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) t = 0 := by
    simpa only [curveVelocity] using
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g γ t hγ hgeo
  have huniq := hinner.unique hzero
  simp only [hvelZero, map_zero, ContinuousLinearMap.zero_apply, zero_add] at huniq
  simpa only [γ, J] using huniq

omit [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem launch_sq_deriv
    (g : SmoothRiemannianMetric I M) (p : M) (u w : E) :
    HasDerivAt
      (fun s : Real => g.inner p (u + s • w) (u + s • w))
      (2 * g.inner p u w) 0 := by
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have hexpand :
      (fun s : Real => g.inner p (u + s • w) (u + s • w)) =
        fun s : Real =>
          gp u u + s * (gp u w + gp w u) + s ^ 2 * gp w w := by
    funext s
    change gp (u + s • w) (u + s • w) = _
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  have hconst : HasDerivAt (fun _ : Real => gp u u) 0 0 :=
    hasDerivAt_const 0 _
  have hlinear :
      HasDerivAt (fun s : Real => s * (gp u w + gp w u))
        (gp u w + gp w u) 0 := by
    simpa using
      (hasDerivAt_id (0 : Real)).mul_const (gp u w + gp w u)
  have hquad : HasDerivAt (fun s : Real => s ^ 2 * gp w w) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : Real)).mul_const (gp w w)
  have hsum :
      HasDerivAt
        (fun s : Real =>
          gp u u + s * (gp u w + gp w u) + s ^ 2 * gp w w)
        (gp u w + gp w u) 0 := by
    simpa using (hconst.add hlinear).add hquad
  have hsymm : gp w u = gp u w := g.symm p w u
  have hvalue : (2 : Real) * gp u w = gp u w + gp w u := by
    rw [hsymm]
    ring
  exact hvalue ▸ hsum

theorem endpointJacobi_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {u w : TangentSpace I p}
    (hu_pos : 0 < g.inner p u u) :
    let F : Real → Real → M := fun s t =>
      intrinsicGeodesic (I := I) g hEnorm p (u + s • w) t
    let γ : Real → M := fun t => F 0 t
    let η : Real → M := fun s => F s 1
    let V : ∀ s, TangentSpace I (η s) := fun s =>
      (intrinsicVelocityLift (I := I) g hEnorm p (u + s • w) 1).snd
    let a : Real → Real := fun s =>
      Real.sqrt (g.inner p (u + s • w) (u + s • w))
    covDerivAlong (I := I) g η (fun s => (a s)⁻¹ • V s) 0 =
      (Real.sqrt (g.inner p u u))⁻¹ •
          covDerivAlong (I := I) g γ
            (intrinsicJacobi (I := I) g hEnorm p u w) 1
        - (g.inner p u w / (Real.sqrt (g.inner p u u)) ^ 3) • V 0 := by
  dsimp only
  let F : Real → Real → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p (u + s • w) t
  let η : Real → M := fun s => F s 1
  let V : ∀ s, TangentSpace I (η s) := fun s =>
    (intrinsicVelocityLift (I := I) g hEnorm p (u + s • w) 1).snd
  let a : Real → Real := fun s =>
    Real.sqrt (g.inner p (u + s • w) (u + s • w))
  have hF : IsSmoothVariation (I := I) F := by
    change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
      (fun q : Real × Real => F q.1 q.2)
    exact
      (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (w : E)).of_le
        ENat.LEInfty.out
  have hVdiff : DifferentiableAt Real
      (chartRepAt (I := I) η V 0) 0 := by
    simpa only [η, V, F, intrinsicVelocityLift] using
      slice_longitudinalField_transverse_chartRep_differentiableAt
        (I := I) F hF 1
  have hsq := launch_sq_deriv (I := I) g p (u : E) (w : E)
  have ha : HasDerivAt a
      ((2 * g.inner p u w) /
        (2 * Real.sqrt (g.inner p u u))) 0 := by
    have hsq_ne :
        g.inner p (u + (0 : Real) • w) (u + (0 : Real) • w) ≠ 0 := by
      simpa only [zero_smul, add_zero] using hu_pos.ne'
    simpa only [a, zero_smul, add_zero] using hsq.sqrt hsq_ne
  have ha0 : a 0 ≠ 0 := by
    simpa only [a, zero_smul, add_zero] using
      Real.sqrt_ne_zero'.mpr hu_pos
  have hainv : HasDerivAt (fun s => (a s)⁻¹)
      (-((2 * g.inner p u w) /
          (2 * Real.sqrt (g.inner p u u))) / (a 0) ^ 2) 0 :=
    ha.inv ha0
  have hsmul :=
    covDerivAlong_smulFun (I := I) g η (fun s => (a s)⁻¹) V 0
      hainv.differentiableAt hVdiff
  have hcomm := commute_ds_dt_intrinsic (I := I) g F hF 1
  rw [hainv.deriv] at hsmul
  have hbase :
      (fun v : Real => F 0 v) =
        fun t => intrinsicGeodesic (I := I) g hEnorm p u t := by
    funext t
    simp only [F, zero_smul, add_zero]
  have hfield :
      (fun v : Real =>
        mfderiv 𝓘(Real, Real) I (fun s : Real => F s v) 0 (1 : Real)) =
        intrinsicJacobi (I := I) g hEnorm p u w := by
    funext t
    rfl
  have hcomm' :
      covDerivAlong (I := I) g η V 0 =
        covDerivAlong (I := I) g
          (fun t => intrinsicGeodesic (I := I) g hEnorm p u t)
          (intrinsicJacobi (I := I) g hEnorm p u w) 1 := by
    rw [hbase, hfield] at hcomm
    simpa only [η, V, intrinsicVelocityLift] using hcomm
  rw [hcomm'] at hsmul
  have ha0_eq :
      a 0 = Real.sqrt (g.inner p u u) := by
    simp only [a, zero_smul, add_zero]
  simp only [ha0_eq] at hsmul
  have hγ0 :
      (fun t =>
        intrinsicGeodesic (I := I) g hEnorm p
          (u + (0 : Real) • w) t) =
        fun t => intrinsicGeodesic (I := I) g hEnorm p u t := by
    funext t
    rw [zero_smul, add_zero]
  have hvel0 :
      (intrinsicVelocityLift (I := I) g hEnorm p
          (u + (0 : Real) • w) 1).snd =
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd := by
    rw [zero_smul, add_zero]
  have hV0 :
      V 0 =
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd := by
    exact hvel0
  rw [hV0] at hsmul
  rw [hsmul]
  rw [hγ0, hvel0]
  have hroot_ne : Real.sqrt (g.inner p u u) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hu_pos
  have hcoef :
      -((2 * g.inner p u w) /
          (2 * Real.sqrt (g.inner p u u))) /
          (Real.sqrt (g.inner p u u)) ^ 2 =
        -(g.inner p u w /
          (Real.sqrt (g.inner p u u)) ^ 3) := by
    field_simp [hroot_ne]
  rw [hcoef, neg_smul]
  abel

theorem branchEnergy_hess
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {p : M}
    (B : ExpInvBranch (I := I) g hEnorm p)
    {u w₁ w₂ : TangentSpace I p}
    (hu : (u : E) ∈ B.hom.source) :
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    let J := fun w => intrinsicJacobi (I := I) g hEnorm p u w
    hessFun (I := I) g
        (branchEnergy (I := I) g B)
        (γ 1) (J w₁ 1) (J w₂ 1) =
      g.inner (γ 1)
        (covDerivAlong (I := I) g γ (J w₁) 1)
        (J w₂ 1) := by
  dsimp only
  let F : Real → Real → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p (u + s • w₁) t
  let γ : Real → M := fun t => F 0 t
  let η : Real → M := fun s => F s 1
  let J : TangentSpace I p → ∀ t, TangentSpace I (γ t) := fun w t =>
    intrinsicJacobi (I := I) g hEnorm p u w t
  let V : ∀ s, TangentSpace I (η s) := fun s =>
    (intrinsicVelocityLift (I := I) g hEnorm p (u + s • w₁) 1).snd
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  have hF : IsSmoothVariation (I := I) F := by
    change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
      (fun z : Real × Real => F z.1 z.2)
    exact
      (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (w₁ : E)).of_le
        ENat.LEInfty.out
  have hη : ContMDiff 𝓘(Real, Real) I ∞ η := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) ∞
        (fun s : Real => (s, (1 : Real))) :=
      contMDiff_id.prodMk contMDiff_const
    exact (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (w₁ : E)).comp
      hincl
  let U : Set M := B.dom
  have hUopen : IsOpen U := B.hom.open_target
  have hqU : q ∈ U := by
    rw [show q = B.hom (u : E) from B.hom_eq hu]
    exact B.hom.map_source hu
  have hinv : ContMDiffOn I 𝓘(Real, E) ∞ B.inv U := by
    simpa only [U] using B.inv_inf
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have hinner : ContMDiffOn I 𝓘(Real, Real) ∞
      (fun z : M => g.inner p (B.inv z) (B.inv z)) U := by
    have hgp : ContMDiffOn I
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun _ : M => gp) U :=
      contMDiffOn_const
    simpa only [gp] using (hgp.clm_apply hinv).clm_apply hinv
  have heU : ContMDiffOn I 𝓘(Real, Real) ∞
      (branchEnergy (I := I) g B) U := by
    simpa only [branchEnergy] using (contMDiffOn_const.mul hinner)
  obtain ⟨eSmooth, heSmooth, he_eq⟩ :=
    DifferentialGeometry.exists_smooth_germ (I := I) hUopen hqU heU
  have hgrad_eq :
      (fun z => gradientFun (I := I) g eSmooth z) =ᶠ[𝓝 q]
        fun z => gradientFun (I := I) g
          (branchEnergy (I := I) g B) z := by
    filter_upwards [he_eq.eventuallyEq_nhds] with z hz
    unfold gradientFun
    rw [hz.mfderiv_eq]
  have hgrad_total :
      (T% fun z => gradientFun (I := I) g eSmooth z) =ᶠ[𝓝 q]
        (T% fun z => gradientFun (I := I) g
          (branchEnergy (I := I) g B) z) := by
    filter_upwards [hgrad_eq] with z hz
    change TotalSpace.mk' E z (gradientFun (I := I) g eSmooth z) =
      TotalSpace.mk' E z
        (gradientFun (I := I) g (branchEnergy (I := I) g B) z)
    rw [hz]
  have hgradSmooth : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (T% fun z => gradientFun (I := I) g eSmooth z) := by
    simpa only [gradient_eq_gradFun] using
      gradFun_contMDiff_total_section (I := I) g heSmooth
  have hgradAt : MDiffAt
      (T% fun z => gradientFun (I := I) g
        (branchEnergy (I := I) g B) z) q := by
    have hsmoothAt :=
      hgradSmooth.contMDiffAt.congr_of_eventuallyEq hgrad_total.symm
    exact hsmoothAt.mdifferentiableAt (by simp)
  have hlaunch : Continuous (fun s : Real => (u : E) + s • (w₁ : E)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hsrc_ev : ∀ᶠ s in 𝓝 (0 : Real),
      (u : E) + s • (w₁ : E) ∈ B.hom.source := by
    have hsrc0 : (u : E) + (0 : Real) • (w₁ : E) ∈ B.hom.source := by
      simpa only [zero_smul, add_zero] using hu
    exact hlaunch.continuousAt (B.hom.open_source.mem_nhds hsrc0)
  have hgrad_ev :
      (fun s => gradientFun (I := I) g
        (branchEnergy (I := I) g B) (η s)) =ᶠ[𝓝 (0 : Real)] V := by
    filter_upwards [hsrc_ev] with s hs
    simpa only [η, F, V, expMapIntrinsic_def] using
      grad_branchEnergy (I := I) B hs
  have hcov_grad :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g η hgrad_ev
  have hchain := covDerivAlong_restrict_eq_leviCivita
    (I := I) g η
      (fun z => gradientFun (I := I) g
        (branchEnergy (I := I) g B) z) 0 hη
      (by
        simpa only [η, F, q, zero_smul, add_zero, expMapIntrinsic_def] using
          hgradAt)
  have hηvel :
      (mfderiv 𝓘(Real, Real) I η 0 : Real →L[Real] TangentSpace I (η 0)) 1 =
        J w₁ 1 := by
    rfl
  have hη0 : η 0 = q := by
    simp only [η, F, q, zero_smul, add_zero, expMapIntrinsic_def]
  have hchain' :
      covDerivAlong (I := I) g η
          (fun s => gradientFun (I := I) g
            (branchEnergy (I := I) g B) (η s)) 0 =
        (LeviCivita (I := I) g).toFun
          (fun z => gradientFun (I := I) g
            (branchEnergy (I := I) g B) z)
          q (J w₁ 1) := by
    rw [hη0] at hηvel hchain
    exact hchain.trans
      (congrArg
        (fun Z : TangentSpace I q =>
          (LeviCivita (I := I) g).toFun
            (fun z => gradientFun (I := I) g
              (branchEnergy (I := I) g B) z) q Z)
        hηvel)
  have hcomm := commute_ds_dt_intrinsic (I := I) g F hF 1
  have hbase :
      (fun t : Real => F 0 t) =
        fun t => intrinsicGeodesic (I := I) g hEnorm p u t := by
    funext t
    simp only [F, zero_smul, add_zero]
  have hfield :
      (fun t : Real =>
        mfderiv 𝓘(Real, Real) I (fun s : Real => F s t) 0 (1 : Real)) =
        intrinsicJacobi (I := I) g hEnorm p u w₁ := by
    funext t
    rfl
  have hcomm' :
      covDerivAlong (I := I) g η V 0 =
        covDerivAlong (I := I) g
          (fun t => intrinsicGeodesic (I := I) g hEnorm p u t)
          (intrinsicJacobi (I := I) g hEnorm p u w₁) 1 := by
    rw [hbase, hfield] at hcomm
    simpa only [η, V, intrinsicVelocityLift] using hcomm
  have hvec :
      (LeviCivita (I := I) g).toFun
          (fun z => gradientFun (I := I) g
            (branchEnergy (I := I) g B) z)
          q (J w₁ 1) =
        covDerivAlong (I := I) g
          (fun t => intrinsicGeodesic (I := I) g hEnorm p u t)
          (intrinsicJacobi (I := I) g hEnorm p u w₁) 1 :=
    hchain'.symm.trans (hcov_grad.trans hcomm')
  have hpair :
      g.inner q
          ((LeviCivita (I := I) g).toFun
            (fun z => gradientFun (I := I) g
              (branchEnergy (I := I) g B) z)
            q (J w₁ 1))
          (J w₂ 1) =
        g.inner q
          (covDerivAlong (I := I) g
            (fun t => intrinsicGeodesic (I := I) g hEnorm p u t)
            (intrinsicJacobi (I := I) g hEnorm p u w₁) 1)
          (J w₂ 1) :=
    congrArg (fun Z : TangentSpace I q => g.inner q Z (J w₂ 1)) hvec
  have hhess :=
    hessFun_eq_cov_local (I := I) g hUopen heU hqU (J w₁ 1) (J w₂ 1)
  simp only [q, J, expMapIntrinsic_def] at hhess hpair ⊢
  exact hhess.trans hpair

theorem branchHess_jacobi
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {p : M}
    (B : ExpInvBranch (I := I) g hEnorm p)
    {u w₁ w₂ : TangentSpace I p}
    (hu : (u : E) ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    let γ : Real → M :=
      intrinsicGeodesic (I := I) g hEnorm p u
    let J := fun w =>
      intrinsicJacobi (I := I) g hEnorm p u w
    let a := Real.sqrt (g.inner p u u)
    hessFun (I := I) g
        (branchRadius (I := I) g B)
        (γ 1) (J w₁ 1) (J w₂ 1)
      =
        g.inner (γ 1)
          (covDerivAlong (I := I) g γ (J w₁) 1)
          (J w₂ 1) / a
        -
        (g.inner p u w₁ * g.inner p u w₂) / a ^ 3 := by
  dsimp only
  let F : Real → Real → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p (u + s • w₁) t
  let γ : Real → M := fun t => F 0 t
  let η : Real → M := fun s => F s 1
  let J : TangentSpace I p → ∀ t, TangentSpace I (γ t) := fun w t =>
    intrinsicJacobi (I := I) g hEnorm p u w t
  let V : ∀ s, TangentSpace I (η s) := fun s =>
    (intrinsicVelocityLift (I := I) g hEnorm p (u + s • w₁) 1).snd
  let a : Real → Real := fun s =>
    Real.sqrt (g.inner p (u + s • w₁) (u + s • w₁))
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  have hη : ContMDiff 𝓘(Real, Real) I ∞ η := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) ∞
        (fun s : Real => (s, (1 : Real))) :=
      contMDiff_id.prodMk contMDiff_const
    exact (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (w₁ : E)).comp
      hincl
  obtain ⟨U, hUopen, hqU, hrU⟩ :=
    branchRadius_open (I := I) B hu hu_pos
  obtain ⟨rSmooth, hrSmooth, hr_eq⟩ :=
    DifferentialGeometry.exists_smooth_germ (I := I) hUopen hqU hrU
  have hgrad_eq :
      (fun z => gradientFun (I := I) g rSmooth z) =ᶠ[𝓝 q]
        fun z => gradientFun (I := I) g
          (branchRadius (I := I) g B) z := by
    filter_upwards [hr_eq.eventuallyEq_nhds] with z hz
    unfold gradientFun
    rw [hz.mfderiv_eq]
  have hgrad_total :
      (T% fun z => gradientFun (I := I) g rSmooth z) =ᶠ[𝓝 q]
        (T% fun z => gradientFun (I := I) g
          (branchRadius (I := I) g B) z) := by
    filter_upwards [hgrad_eq] with z hz
    change
      TotalSpace.mk' E z (gradientFun (I := I) g rSmooth z) =
        TotalSpace.mk' E z
          (gradientFun (I := I) g
            (branchRadius (I := I) g B) z)
    rw [hz]
  have hgradSmooth : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (T% fun z => gradientFun (I := I) g rSmooth z) := by
    simpa only [gradient_eq_gradFun] using
      gradFun_contMDiff_total_section (I := I) g hrSmooth
  have hgradAt : MDiffAt
      (T% fun z => gradientFun (I := I) g
        (branchRadius (I := I) g B) z) q := by
    have hsmoothAt :=
      hgradSmooth.contMDiffAt.congr_of_eventuallyEq hgrad_total.symm
    exact hsmoothAt.mdifferentiableAt (by simp)
  have hlaunch : Continuous (fun s : Real => (u : E) + s • (w₁ : E)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hsrc_ev : ∀ᶠ s in 𝓝 (0 : Real),
      (u : E) + s • (w₁ : E) ∈ B.hom.source := by
    have hsrc0 :
        (u : E) + (0 : Real) • (w₁ : E) ∈ B.hom.source := by
      simpa only [zero_smul, add_zero] using hu
    exact hlaunch.continuousAt (B.hom.open_source.mem_nhds hsrc0)
  have hsq_cont : Continuous
      (fun s : Real => g.inner p (u + s • w₁) (u + s • w₁)) := by
    fun_prop
  have hpos_ev : ∀ᶠ s in 𝓝 (0 : Real),
      0 < g.inner p (u + s • w₁) (u + s • w₁) := by
    have hpos0 :
        0 <
          g.inner p (u + (0 : Real) • w₁)
            (u + (0 : Real) • w₁) := by
      simpa only [zero_smul, add_zero] using hu_pos
    exact hsq_cont.continuousAt (isOpen_Ioi.mem_nhds hpos0)
  have hgrad_ev :
      (fun s => gradientFun (I := I) g
        (branchRadius (I := I) g B) (η s)) =ᶠ[𝓝 (0 : Real)]
      (fun s => (a s)⁻¹ • V s) := by
    filter_upwards [hsrc_ev, hpos_ev] with s hs hsp
    simpa only [η, F, a, V, expMapIntrinsic_def] using
      grad_branchRadius (I := I) B hs hsp
  have hcov_grad :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g η hgrad_ev
  have hchain := covDerivAlong_restrict_eq_leviCivita
    (I := I) g η
      (fun z => gradientFun (I := I) g
        (branchRadius (I := I) g B) z) 0 hη
      (by
        simpa only [η, F, q, zero_smul, add_zero, expMapIntrinsic_def] using
          hgradAt)
  have hηvel :
      (mfderiv 𝓘(Real, Real) I η 0 : Real →L[Real] TangentSpace I (η 0)) 1 =
        J w₁ 1 := by
    rfl
  have hη0 : η 0 = q := by
    simp only [η, F, q, zero_smul, add_zero, expMapIntrinsic_def]
  have hchain' :
      covDerivAlong (I := I) g η
          (fun s => gradientFun (I := I) g
            (branchRadius (I := I) g B) (η s)) 0 =
        (LeviCivita (I := I) g).toFun
          (fun z => gradientFun (I := I) g
            (branchRadius (I := I) g B) z)
          q (J w₁ 1) := by
    rw [hη0] at hηvel hchain
    exact hchain.trans
      (congrArg
        (fun Z : TangentSpace I q =>
          (LeviCivita (I := I) g).toFun
            (fun z => gradientFun (I := I) g
              (branchRadius (I := I) g B) z) q Z)
        hηvel)
  have hend := endpointJacobi_eq (I := I) g hEnorm p
    (u := u) (w := w₁) hu_pos
  have hend' :
      covDerivAlong (I := I) g η (fun s => (a s)⁻¹ • V s) 0 =
        (Real.sqrt (g.inner p u u))⁻¹ •
            covDerivAlong (I := I) g γ (J w₁) 1
          - (g.inner p u w₁ /
              (Real.sqrt (g.inner p u u)) ^ 3) • V 0 := by
    simpa only [F, γ, η, V, a, J, zero_smul, add_zero] using hend
  have hV0 :
      V 0 =
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd := by
    change
      (intrinsicVelocityLift (I := I) g hEnorm p
          (u + (0 : Real) • w₁) 1).snd =
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd
    rw [zero_smul, add_zero]
  have hgauss :
      g.inner q (V 0) (J w₂ 1) = g.inner p u w₂ := by
    rw [hV0]
    simpa only [q, J, expMapIntrinsic_def] using
      intrinsicJacobi_perp (I := I) g hEnorm p u w₂
  have hvec :
      (LeviCivita (I := I) g).toFun
          (fun z => gradientFun (I := I) g
            (branchRadius (I := I) g B) z)
          q (J w₁ 1) =
        (Real.sqrt (g.inner p u u))⁻¹ •
            covDerivAlong (I := I) g γ (J w₁) 1
          - (g.inner p u w₁ /
              (Real.sqrt (g.inner p u u)) ^ 3) • V 0 :=
    hchain'.symm.trans (hcov_grad.trans hend')
  have hinner_sub (X Y Z : TangentSpace I q) :
      g.inner q (X - Y) Z = g.inner q X Z - g.inner q Y Z := by
    rw [g.symm q (X - Y) Z, g.symm q X Z, g.symm q Y Z]
    exact ContinuousLinearMap.map_sub (g.inner q Z) X Y
  have hinner_smul (r : Real) (X Z : TangentSpace I q) :
      g.inner q (r • X) Z = r * g.inner q X Z := by
    rw [g.symm q (r • X) Z, g.symm q X Z]
    simpa only [smul_eq_mul] using
      (g.inner q Z).map_smul r X
  have hpair :
      g.inner q
          ((LeviCivita (I := I) g).toFun
            (fun z => gradientFun (I := I) g
              (branchRadius (I := I) g B) z)
            q (J w₁ 1))
          (J w₂ 1) =
        (Real.sqrt (g.inner p u u))⁻¹ *
            g.inner q
              (covDerivAlong (I := I) g γ (J w₁) 1)
              (J w₂ 1)
          - (g.inner p u w₁ /
              (Real.sqrt (g.inner p u u)) ^ 3) *
              g.inner q (V 0) (J w₂ 1) := by
    calc
      _ = g.inner q
          ((Real.sqrt (g.inner p u u))⁻¹ •
              covDerivAlong (I := I) g γ (J w₁) 1
            - (g.inner p u w₁ /
                (Real.sqrt (g.inner p u u)) ^ 3) • V 0)
          (J w₂ 1) :=
        congrArg
          (fun Z : TangentSpace I q => g.inner q Z (J w₂ 1)) hvec
      _ = g.inner q
            ((Real.sqrt (g.inner p u u))⁻¹ •
              covDerivAlong (I := I) g γ (J w₁) 1)
            (J w₂ 1)
          - g.inner q
            ((g.inner p u w₁ /
              (Real.sqrt (g.inner p u u)) ^ 3) • V 0)
            (J w₂ 1) :=
        hinner_sub _ _ _
      _ = _ := by
        exact congrArg₂ (fun x y : Real => x - y)
          (hinner_smul _ _ _)
          (hinner_smul _ _ _)
  rw [hgauss] at hpair
  have hγeq :
      γ = intrinsicGeodesic (I := I) g hEnorm p u := by
    funext t
    simp only [γ, F, zero_smul, add_zero]
  rw [hγeq] at hpair
  simp only [q, J, expMapIntrinsic_def] at hpair
  have hJeq :
      (fun t : Real => intrinsicJacobi (I := I) g hEnorm p u w₁ t) =
        intrinsicJacobi (I := I) g hEnorm p u w₁ := by
    funext t
    rfl
  rw [hJeq] at hpair
  have hhess :=
    hessFun_eq_cov_local (I := I) g hUopen hrU hqU
      (J w₁ 1) (J w₂ 1)
  simp only [J, expMapIntrinsic_def] at hhess ⊢
  refine hhess.trans ?_
  have hpair' := hpair
  simp only [gradient_eq_gradFun] at hpair'
  rw [hpair']
  have hroot_ne : Real.sqrt (g.inner p u u) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_pos)
  field_simp [hroot_ne]
  rfl

theorem branchHess_shape
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {p : M}
    (B : ExpInvBranch (I := I) g hEnorm p)
    {u w₁ w₂ : TangentSpace I p}
    (hu : (u : E) ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u)
    (hw₁ : g.inner p u w₁ = 0)
    (hw₂ : g.inner p u w₂ = 0) :
    let γ : Real → M :=
      intrinsicGeodesic (I := I) g hEnorm p u
    let J := fun w =>
      intrinsicJacobi (I := I) g hEnorm p u w
    hessFun (I := I) g
        (branchRadius (I := I) g B)
        (γ 1) (J w₁ 1) (J w₂ 1)
      =
        g.inner (γ 1)
          (covDerivAlong (I := I) g γ (J w₁) 1)
          (J w₂ 1) /
        Real.sqrt (g.inner p u u) := by
  dsimp only
  rw [branchHess_jacobi (I := I) B hu hu_pos
    (w₁ := w₁) (w₂ := w₂), hw₁, hw₂]
  ring

theorem intrinsicJacobi_li
    {ι : Type*}
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {p : M}
    (B : ExpInvBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : (u : E) ∈ B.hom.source)
    (v : ι → TangentSpace I p)
    (hv : LinearIndependent Real v) :
    LinearIndependent Real fun i =>
      intrinsicJacobi (I := I) g hEnorm p u (v i) 1 := by
  let expf : E → M := fun w =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from w)
  let L : E →L[Real] E :=
    mfderiv 𝓘(Real, E) I expf (u : E)
  let invf : M → E := B.inv
  let dInv : E → E := fun Y =>
    mfderiv I 𝓘(Real, E) invf
      (expMapIntrinsic (I := I) g hEnorm p u)
      (show TangentSpace I
        (expMapIntrinsic (I := I) g hEnorm p u) from Y)
  have hleft (w : E) : dInv (L w) = w := by
    simpa only [dInv, L, expf, invf] using
      inv_exp_mfderiv (I := I) B hu
        (show TangentSpace I p from w)
  have hLinj : Function.Injective L := by
    intro w₁ w₂ hw
    calc
      w₁ = dInv (L w₁) := (hleft w₁).symm
      _ = dInv (L w₂) := congrArg dInv hw
      _ = w₂ := hleft w₂
  have hmapped : LinearIndependent Real fun i => L (v i : E) :=
    hv.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hLinj)
  have hfield :
      (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i) 1) =
        fun i => L (v i : E) := by
    funext i
    simpa only [intrinsicJacobi, L, expf] using
      intrinsic_jacobi_one (I := I) g hEnorm p (u : E) (v i : E)
  rw [hfield]
  exact hmapped

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
