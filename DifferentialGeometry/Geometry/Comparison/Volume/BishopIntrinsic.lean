import DifferentialGeometry.Geometry.Comparison.Volume.BishopRadial
import DifferentialGeometry.Geometry.Comparison.RadialLaplacian
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Intrinsic Bishop comparison along a complete radial geodesic

This file removes the chart-radius restriction from the radial mean-curvature
comparison.  The raw exponential is used only through its germ at the pole;
all Jacobi, nonconjugacy, and Riccati data on the positive interval belong to
the complete intrinsic geodesic.
-/

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open CovariantDerivativeAlong
open Exponential
open Geodesic
open Variation
open BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Near the pole, the complete intrinsic radial geodesic and its
initial-velocity Jacobi field agree with the chart-fixed realizations. -/
theorem intrJacobi_raw
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w : E) :
    ∀ᶠ t in 𝓝[>] (0 : Real),
      intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u) t =
        radialCurve (I := I) g p u t ∧
      (intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from u)
          (show TangentSpace I p from w) t : E) =
        (radialJacobiField (I := I) g p u w t : E) := by
  have htend :
      Tendsto (fun t : Real => t • u) (𝓝[>] (0 : Real)) (𝓝 (0 : E)) := by
    have hcont : Continuous fun t : Real => t • u :=
      continuous_id.smul continuous_const
    have hzero :
        Tendsto (fun t : Real => t • u) (𝓝 (0 : Real)) (𝓝 (0 : E)) := by
      simpa using (hcont.continuousAt (x := (0 : Real))).tendsto
    exact hzero.mono_left inf_le_left
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : Real),
      ‖t • u‖ < expMapC2Radius (I := I) g p := by
    have hball := htend.eventually
      (Metric.ball_mem_nhds (0 : E) (expMapC2Radius_pos (I := I) g p))
    filter_upwards [hball] with t ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  filter_upwards [hsmall] with t ht
  constructor
  · calc
      intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u) t =
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from t • u) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm p
          (show TangentSpace I p from u) t).symm
      _ = expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from t • u) := rfl
      _ = expMap (I := I) g p
          (show TangentSpace I p from t • u) :=
        (exp_eq_intr_of_c2 (I := I) g hEnorm p ht).symm
      _ = radialCurve (I := I) g p u t := rfl
  · have hgerm :=
      exp_germ_eq_intr (I := I) g hEnorm p ht
    have hmf := Filter.EventuallyEq.mfderiv_eq
      (I := 𝓘(Real, E)) (I' := I) hgerm
    have happ :=
      congrArg (fun L : E →L[Real] E => L (t • w)) hmf
    have hraw :=
      radialJacobi_at (I := I) g p u w t ht
    have hintr :=
      intrinsic_jacobi_at (I := I) g hEnorm p u w t
    rw [hraw]
    exact hintr.trans happ.symm

private theorem linIndep_of_ortho
    {ι : Type*} [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : ι → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    LinearIndependent Real v := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  have hpair := congrArg (fun z : E => g.inner p z (v j)) hc
  change g.inner p (∑ i ∈ s, c i • v i) (v j) =
    g.inner p 0 (v j) at hpair
  rw [map_sum, ContinuousLinearMap.sum_apply, map_zero,
    ContinuousLinearMap.zero_apply] at hpair
  have hsummand : ∀ i ∈ s,
      g.inner p (c i • v i) (v j) =
        c i * (if i = j then 1 else 0) := by
    intro i _
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hON i j]
  rw [Finset.sum_congr rfl hsummand] at hpair
  rw [Finset.sum_eq_single_of_mem j hj] at hpair
  · simpa only [if_pos, mul_one] using hpair
  · intro i _ hij
    rw [if_neg (by simpa using hij), mul_zero]

private theorem intrVar_smooth
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w : TangentSpace I p) :
    IsSmoothVariation (I := I) fun s t =>
      intrinsicGeodesic (I := I) g hEnorm p (u + s • w) t := by
  change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
    (fun q : Real × Real =>
      intrinsicGeodesic (I := I) g hEnorm p (u + q.1 • w) q.2)
  exact (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (w : E)).of_le
    ENat.LEInfty.out

private theorem intrJacobi_diff
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
  have hF : IsSmoothVariation (I := I) F :=
    intrVar_smooth (I := I) g hEnorm p u w
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
      variationField_chartRep_differentiableAt (I := I) g F hF t
    rw [hbase, hfield] at h
    exact h
  · have h :=
      variationField_covDeriv_chartRep_differentiableAt (I := I) g F hF t
    rw [hbase, hfield] at h
    exact h

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
      (Filter.univ_mem)).mdifferentiableAt (by norm_num)
  have hvel := curveVelocity_comp_mul (I := I) γ c 1 hγ
  change
    (curveVelocity (I := I)
      (fun s => intrinsicGeodesic (I := I) g hEnorm p (c • u) s) 1 : E) =
      c • (curveVelocity (I := I) γ c : E)
  rw [hfun]
  have hct : c * 1 = c := mul_one c
  rw [hct] at hvel
  exact hvel

private theorem intrJacobi_perp_ne
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
    intrinsicJacobi_perp (I := I) g hEnorm p
      (t • u) (t • w)
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

private theorem intrGeodesic_smooth
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u : TangentSpace I p) :
    ContMDiff 𝓘(Real, Real) I (8 : Nat)
      (intrinsicGeodesic (I := I) g hEnorm p u) := by
  let F : Real → Real → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p (u + s • (0 : TangentSpace I p)) t
  have hF : IsSmoothVariation (I := I) F :=
    intrVar_smooth (I := I) g hEnorm p u 0
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

private theorem intrJacobi_dperp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w : TangentSpace I p) {t : Real}
    (ht : t ≠ 0) (hperp : g.inner p u w = 0)
    (hJdiff : DifferentiableAt Real
      (chartRepAt (I := I)
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (intrinsicJacobi (I := I) g hEnorm p u w) t) t) :
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
  have hinner := inner_deriv_at (I := I) (n := (2 : WithTop ℕ∞))
    (by norm_num) g γ (curveVelocity (I := I) γ) J t hγ hvelDiff (by
      simpa only [γ, J] using hJdiff)
  have hne : ∀ᶠ s in 𝓝 t, s ≠ 0 :=
    eventually_ne_nhds ht
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
    (hasDerivAt_const (x := t) (c := (0 : Real))).congr_of_eventuallyEq
      hzeroEv
  have hvelZero :
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) t = 0 := by
    simpa only [curveVelocity] using
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g γ t hγ hgeo
  have huniq := hinner.unique hzero
  simp only [hvelZero, map_zero, ContinuousLinearMap.zero_apply, zero_add] at huniq
  simpa only [γ, J] using huniq

private theorem intrWronsk_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w₁ w₂ : TangentSpace I p) (b : Real) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      jacobiWronskian (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (intrinsicJacobi (I := I) g hEnorm p u w₁)
        (intrinsicJacobi (I := I) g hEnorm p u w₂) t = 0 := by
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let J := intrinsicJacobi (I := I) g hEnorm p u w₁
  let K := intrinsicJacobi (I := I) g hEnorm p u w₂
  have hγInf : ContMDiff 𝓘(Real, Real) I (8 : Nat) γ :=
    intrGeodesic_smooth (I := I) g hEnorm p u
  have hγ : ∀ t ∈ Set.Icc (0 : Real) b,
      ContMDiffAt 𝓘(Real, Real) I (2 : WithTop ℕ∞) γ t := by
    intro t ht
    exact hγInf.contMDiffAt.of_le (by norm_num)
  have hJdiff : ∀ t ∈ Set.Icc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) γ J t) t := by
    intro t ht
    simpa only [γ, J] using
      (intrJacobi_diff (I := I) g hEnorm p u w₁ t).1
  have hKdiff : ∀ t ∈ Set.Icc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) γ K t) t := by
    intro t ht
    simpa only [γ, K] using
      (intrJacobi_diff (I := I) g hEnorm p u w₂ t).1
  have hDJdiff : ∀ t ∈ Set.Icc (0 : Real) b,
      DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ J s) t) t := by
    intro t ht
    simpa only [γ, J] using
      (intrJacobi_diff (I := I) g hEnorm p u w₁ t).2
  have hDKdiff : ∀ t ∈ Set.Icc (0 : Real) b,
      DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ K s) t) t := by
    intro t ht
    simpa only [γ, K] using
      (intrJacobi_diff (I := I) g hEnorm p u w₂ t).2
  have hJacJ : ∀ t ∈ Set.Icc (0 : Real) b,
      IsJacobiAt (I := I) g γ J t := by
    intro t ht
    simpa only [γ, J] using
      intrinsic_jacobi (I := I) g hEnorm p (u : E) (w₁ : E) t
  have hJacK : ∀ t ∈ Set.Icc (0 : Real) b,
      IsJacobiAt (I := I) g γ K t := by
    intro t ht
    simpa only [γ, K] using
      intrinsic_jacobi (I := I) g hEnorm p (u : E) (w₂ : E) t
  have hJ0 : J 0 = 0 := by
    simpa only [γ, J, intrinsicJacobi] using
      jacobiVar_zero (I := I) g hEnorm p (u : E) (w₁ : E)
  have hK0 : K 0 = 0 := by
    simpa only [γ, K, intrinsicJacobi] using
      jacobiVar_zero (I := I) g hEnorm p (u : E) (w₂ : E)
  simpa only [γ, J, K] using
    wronskian_zero_on (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ J K hγ hJdiff hKdiff hDJdiff hDKdiff hJacJ hJacK hJ0 hK0

private theorem intrJacobi_li
    {ι : Type*}
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u : TangentSpace I p) (v : ι → TangentSpace I p)
    (hv : LinearIndependent Real v) {t : Real} (ht : t ≠ 0)
    (hno : ¬ IsConjVec (I := I) g hEnorm p (t • (u : E))) :
    LinearIndependent Real fun i =>
      intrinsicJacobi (I := I) g hEnorm p u (v i) t := by
  let L : E →L[Real] E :=
    mfderiv 𝓘(Real, E) I
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z))
      (t • (u : E))
  have hLinj : Function.Injective L := by
    unfold IsConjVec at hno
    exact Classical.not_not.mp hno
  let a : Realˣ := Units.mk0 t ht
  let as : ι → Realˣ := fun _ => a
  have hscaled : LinearIndependent Real fun i => t • v i := by
    have has : as • v = fun i => t • v i := by
      funext i
      rfl
    rw [← has]
    exact hv.units_smul as
  have hmapped : LinearIndependent Real fun i => L (t • (v i : E)) :=
    hscaled.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hLinj)
  have hfield :
      (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i) t) =
        fun i => L (t • (v i : E)) := by
    funext i
    simpa only [L] using
      intrinsic_jacobi_at (I := I) g hEnorm p (u : E) (v i : E) t
  rw [hfield]
  exact hmapped

/-- Whole-tail intrinsic Bishop comparison.  The raw exponential is used only
as a germ at the pole; nonconjugacy and the Riccati argument run along the
complete intrinsic geodesic. -/
theorem exists_intrMean
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q b : Real)
    (hq : 0 ≤ q) (hb : 1 < b)
    (hu : 0 < g.inner p u u)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ v : Fin (Module.finrank Real E - 1) → TangentSpace I p,
      LinearIndependent Real v ∧
      (∀ i, g.inner p u (v i) = 0) ∧
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
      let ell := Real.sqrt (g.inner p u u)
      curveMean (I := I) g γ V 1 / ell ≤
        ((Module.finrank Real E - 1 : Nat) : Real) / ell +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  classical
  let d : Nat := Module.finrank Real E - 1
  by_cases hd0 : d = 0
  · let v : Fin d → TangentSpace I p := fun i => Fin.elim0 (hd0 ▸ i)
    have hv : LinearIndependent Real v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      exact Fin.elim0 (hd0 ▸ i)
    have hperp : ∀ i, g.inner p u (v i) = 0 := by
      intro i
      exact Fin.elim0 (hd0 ▸ i)
    refine ⟨v, hv, hperp, ?_⟩
    have hmean0 :
        curveMean (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) 1 = 0 := by
      simp only [curveMean, Matrix.trace]
      apply Finset.sum_eq_zero
      intro i hi
      exact Fin.elim0 (hd0 ▸ i)
    simp only [d, hd0, Nat.cast_zero, zero_div, zero_mul, add_zero,
      hmean0]
    exact le_rfl
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p u hu
    have hperp : ∀ i, g.inner p u (v i) = 0 := by
      intro i
      rw [g.symm p u (v i)]
      exact hperp' i
    have hv : LinearIndependent Real v :=
      linIndep_of_ortho (I := I) g p v hON
    refine ⟨v, hv, hperp, ?_⟩
    let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
    let V : Fin d → ∀ t, TangentSpace I (γ t) := fun i =>
      intrinsicJacobi (I := I) g hEnorm p u (v i)
    let ell : Real := Real.sqrt (g.inner p u u)
    have hell : 0 < ell := by
      simpa only [ell] using Real.sqrt_pos.2 hu
    have hγInf : ContMDiff 𝓘(Real, Real) I (8 : Nat) γ :=
      intrGeodesic_smooth (I := I) g hEnorm p u
    have hγ : ∀ t ∈ Set.Ioo (0 : Real) b,
        ContMDiffAt 𝓘(Real, Real) I (2 : WithTop ℕ∞) γ t := by
      intro t ht
      exact hγInf.contMDiffAt.of_le (by norm_num)
    have hspeed : ∀ t ∈ Set.Ioo (0 : Real) b,
        g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) = ell ^ 2 := by
      intro t ht
      calc
        g.inner (γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) =
            g.inner p u u := by
          simpa only [γ, curveVelocity] using
            intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t
        _ = ell ^ 2 := (Real.sq_sqrt hu.le).symm
    have hVdiff : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        DifferentiableAt Real (chartRepAt (I := I) γ (V i) t) t := by
      intro t ht i
      simpa only [γ, V] using
        (intrJacobi_diff (I := I) g hEnorm p u (v i) t).1
    have hDVdiff : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        DifferentiableAt Real
          (chartRepAt (I := I) γ
            (fun s => covDerivAlong (I := I) g γ (V i) s) t) t := by
      intro t ht i
      simpa only [γ, V] using
        (intrJacobi_diff (I := I) g hEnorm p u (v i) t).2
    have hVperp : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
      intro t ht i
      simpa only [γ, V] using
        intrJacobi_perp_ne (I := I) g hEnorm p u (v i) ht.1.ne' (hperp i)
    have hDVperp : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        g.inner (γ t) (curveVelocity (I := I) γ t)
          (covDerivAlong (I := I) g γ (V i) t) = 0 := by
      intro t ht i
      simpa only [γ, V] using
        intrJacobi_dperp (I := I) g hEnorm p u (v i) ht.1.ne'
          (hperp i) (hVdiff t ht i)
    have hLI : ∀ t ∈ Set.Ioo (0 : Real) b,
        LinearIndependent Real fun i => V i t := by
      intro t ht
      simpa only [γ, V] using
        intrJacobi_li (I := I) g hEnorm p u v hv ht.1.ne' (hno t ht)
    have hW : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i j,
        jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
      intro t ht i j
      simpa only [γ, V] using
        intrWronsk_zero (I := I) g hEnorm p u (v i) (v j) b t
          ⟨ht.1.le, ht.2.le⟩
    have hJ : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
        IsJacobiAt (I := I) g γ (V i) t := by
      intro t ht i
      simpa only [γ, V] using
        intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) t
    have hRatio : ∃ C : Real, 0 < C ∧
        ∀ᶠ t in 𝓝[>] (0 : Real),
          C ≤ curveDensity (I := I) g γ V t /
            hypDensity (q * ell) d t := by
      obtain ⟨C, hC, hraw⟩ :=
        radialRatio_auto (I := I) g p (u : E) (fun i => (v i : E))
          (q * ell) (mul_nonneg hq hell.le) hv
      have hcurve :
          ∀ᶠ t in 𝓝[>] (0 : Real),
            γ t = radialCurve (I := I) g p (u : E) t := by
        filter_upwards [intrJacobi_raw (I := I) g hEnorm p (u : E) (0 : E)]
          with t ht
        simpa only [γ] using ht.1
      have hfield_i : ∀ i,
          ∀ᶠ t in 𝓝[>] (0 : Real),
            (V i t : E) =
              (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) := by
        intro i
        filter_upwards [
          intrJacobi_raw (I := I) g hEnorm p (u : E) (v i : E)] with t ht
        simpa only [V] using ht.2
      have hfields :
          ∀ᶠ t in 𝓝[>] (0 : Real), ∀ i,
            (V i t : E) =
              (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) :=
        Filter.eventually_all.2 hfield_i
      refine ⟨C, hC, ?_⟩
      filter_upwards [hraw, hcurve, hfields] with t hrt hct hft
      have hgram :
          curveGram (I := I) g γ V t =
            curveGram (I := I) g
              (radialCurve (I := I) g p (u : E))
              (fun i => radialJacobiField (I := I) g p
                (u : E) (v i : E)) t := by
        ext i j
        simp only [curveGram, Matrix.of_apply]
        rw [hct, hft i, hft j]
      calc
        C ≤ curveDensity (I := I) g
              (radialCurve (I := I) g p (u : E))
              (fun i => radialJacobiField (I := I) g p
                (u : E) (v i : E)) t /
              hypDensity (q * ell) (Fintype.card (Fin d)) t := hrt
        _ = curveDensity (I := I) g γ V t /
              hypDensity (q * ell) d t := by
          rw [Fintype.card_fin]
          simp only [curveDensity, hgram]
    have hmean := curveMean_le_hyp
      (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ V q ell b hq hell (Fintype.card_fin d) hd hγ hspeed
      hVperp hDVperp hVdiff hDVdiff hLI hW hJ hRic hRatio
    have hone : (1 : Real) ∈ Set.Ioo (0 : Real) b :=
      ⟨zero_lt_one, hb⟩
    have hmean1 := hmean 1 hone
    have hhyp :=
      hypMeanCurv_le d (mul_nonneg hq hell.le) (by norm_num : (0 : Real) < 1)
    have hrawBound :
        curveMean (I := I) g γ V 1 ≤
          (d : Real) + (d : Real) * q * ell := by
      calc
        curveMean (I := I) g γ V 1 ≤
            hypMeanCurv (q * ell) d 1 := hmean1
        _ ≤ (d : Real) / 1 + (d : Real) * (q * ell) := hhyp
        _ = (d : Real) + (d : Real) * q * ell := by ring
    apply (div_le_iff₀ hell).2
    calc
      curveMean (I := I) g γ V 1 ≤
          (d : Real) + (d : Real) * q * ell := hrawBound
      _ = ((d : Real) / ell + (d : Real) * q) * ell := by
        rw [add_mul, div_mul_cancel₀ _ hell.ne']

/-- Whole-tail intrinsic Bishop ratio monotonicity.  Companion to
`exists_intrMean`: for the same transverse Jacobi frame the density ratio to the
hyperbolic model is antitone along the complete intrinsic geodesic.  The speed
`ell = √(g.inner p u u)` scales the model, so the comparison is against
`hypDensity (q * ell)`.  Assumes a positive transverse dimension (dropping the
degenerate `finrank = 1` case that `exists_intrMean` handles). -/
theorem exists_intrRatio
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q b : Real)
    (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ v : Fin (Module.finrank Real E - 1) → TangentSpace I p,
      LinearIndependent Real v ∧
      (∀ i, g.inner p u (v i) = 0) ∧
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
      let ell := Real.sqrt (g.inner p u u)
      AntitoneOn
        (fun t => curveDensity (I := I) g γ V t /
          hypDensity (q * ell) (Module.finrank Real E - 1) t)
        (Set.Ioo (0 : Real) b) := by
  classical
  let d : Nat := Module.finrank Real E - 1
  obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p u hu
  have hperp : ∀ i, g.inner p u (v i) = 0 := by
    intro i
    rw [g.symm p u (v i)]
    exact hperp' i
  have hv : LinearIndependent Real v :=
    linIndep_of_ortho (I := I) g p v hON
  refine ⟨v, hv, hperp, ?_⟩
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let V : Fin d → ∀ t, TangentSpace I (γ t) := fun i =>
    intrinsicJacobi (I := I) g hEnorm p u (v i)
  let ell : Real := Real.sqrt (g.inner p u u)
  have hell : 0 < ell := by
    simpa only [ell] using Real.sqrt_pos.2 hu
  have hγInf : ContMDiff 𝓘(Real, Real) I (8 : Nat) γ :=
    intrGeodesic_smooth (I := I) g hEnorm p u
  have hγ : ∀ t ∈ Set.Ioo (0 : Real) b,
      ContMDiffAt 𝓘(Real, Real) I (2 : WithTop ℕ∞) γ t := by
    intro t ht
    exact hγInf.contMDiffAt.of_le (by norm_num)
  have hspeed : ∀ t ∈ Set.Ioo (0 : Real) b,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = ell ^ 2 := by
    intro t ht
    calc
      g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) =
          g.inner p u u := by
        simpa only [γ, curveVelocity] using
          intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t
      _ = ell ^ 2 := (Real.sq_sqrt hu.le).symm
  have hVdiff : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      DifferentiableAt Real (chartRepAt (I := I) γ (V i) t) t := by
    intro t ht i
    simpa only [γ, V] using
      (intrJacobi_diff (I := I) g hEnorm p u (v i) t).1
  have hDVdiff : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t := by
    intro t ht i
    simpa only [γ, V] using
      (intrJacobi_diff (I := I) g hEnorm p u (v i) t).2
  have hVperp : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
    intro t ht i
    simpa only [γ, V] using
      intrJacobi_perp_ne (I := I) g hEnorm p u (v i) ht.1.ne' (hperp i)
  have hDVperp : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0 := by
    intro t ht i
    simpa only [γ, V] using
      intrJacobi_dperp (I := I) g hEnorm p u (v i) ht.1.ne'
        (hperp i) (hVdiff t ht i)
  have hLI : ∀ t ∈ Set.Ioo (0 : Real) b,
      LinearIndependent Real fun i => V i t := by
    intro t ht
    simpa only [γ, V] using
      intrJacobi_li (I := I) g hEnorm p u v hv ht.1.ne' (hno t ht)
  have hW : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i j,
      jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
    intro t ht i j
    simpa only [γ, V] using
      intrWronsk_zero (I := I) g hEnorm p u (v i) (v j) b t
        ⟨ht.1.le, ht.2.le⟩
  have hJ : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t := by
    intro t ht i
    simpa only [γ, V] using
      intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) t
  have hRatio : ∃ C : Real, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : Real),
        C ≤ curveDensity (I := I) g γ V t /
          hypDensity (q * ell) d t := by
    obtain ⟨C, hC, hraw⟩ :=
      radialRatio_auto (I := I) g p (u : E) (fun i => (v i : E))
        (q * ell) (mul_nonneg hq hell.le) hv
    have hcurve :
        ∀ᶠ t in 𝓝[>] (0 : Real),
          γ t = radialCurve (I := I) g p (u : E) t := by
      filter_upwards [intrJacobi_raw (I := I) g hEnorm p (u : E) (0 : E)]
        with t ht
      simpa only [γ] using ht.1
    have hfield_i : ∀ i,
        ∀ᶠ t in 𝓝[>] (0 : Real),
          (V i t : E) =
            (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) := by
      intro i
      filter_upwards [
        intrJacobi_raw (I := I) g hEnorm p (u : E) (v i : E)] with t ht
      simpa only [V] using ht.2
    have hfields :
        ∀ᶠ t in 𝓝[>] (0 : Real), ∀ i,
          (V i t : E) =
            (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) :=
      Filter.eventually_all.2 hfield_i
    refine ⟨C, hC, ?_⟩
    filter_upwards [hraw, hcurve, hfields] with t hrt hct hft
    have hgram :
        curveGram (I := I) g γ V t =
          curveGram (I := I) g
            (radialCurve (I := I) g p (u : E))
            (fun i => radialJacobiField (I := I) g p
              (u : E) (v i : E)) t := by
      ext i j
      simp only [curveGram, Matrix.of_apply]
      rw [hct, hft i, hft j]
    calc
      C ≤ curveDensity (I := I) g
            (radialCurve (I := I) g p (u : E))
            (fun i => radialJacobiField (I := I) g p
              (u : E) (v i : E)) t /
            hypDensity (q * ell) (Fintype.card (Fin d)) t := hrt
      _ = curveDensity (I := I) g γ V t /
            hypDensity (q * ell) d t := by
        rw [Fintype.card_fin]
        simp only [curveDensity, hgram]
  have hmean := curveMean_le_hyp
    (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V q ell b hq hell (Fintype.card_fin d) hd hγ hspeed
    hVperp hDVperp hVdiff hDVdiff hLI hW hJ hRic hRatio
  exact curveRatio_anti (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V (q * ell) b d (mul_nonneg hq hell.le) hγ hVdiff hLI hW hmean

/-- Frame-input companion to `exists_intrRatio`.  Given a `gₓ`-orthonormal
transverse frame `v` (perpendicular to `u`), the transverse-Jacobi density ratio
to the speed-scaled hyperbolic model is antitone along the complete intrinsic
geodesic.  Exposing the frame lets a caller feed the SAME frame to the sharp
pole-limit lemma, so the antitone bound and the pole limit refer to one frame. -/
theorem intrRatioOfFrame
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q b : Real)
    (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
    let ell := Real.sqrt (g.inner p u u)
    AntitoneOn
      (fun t => curveDensity (I := I) g γ V t /
        hypDensity (q * ell) (Module.finrank Real E - 1) t)
      (Set.Ioo (0 : Real) b) := by
  classical
  let d : Nat := Module.finrank Real E - 1
  have hv : LinearIndependent Real v :=
    linIndep_of_ortho (I := I) g p v hON
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let V : Fin d → ∀ t, TangentSpace I (γ t) := fun i =>
    intrinsicJacobi (I := I) g hEnorm p u (v i)
  let ell : Real := Real.sqrt (g.inner p u u)
  have hell : 0 < ell := by
    simpa only [ell] using Real.sqrt_pos.2 hu
  have hγInf : ContMDiff 𝓘(Real, Real) I (8 : Nat) γ :=
    intrGeodesic_smooth (I := I) g hEnorm p u
  have hγ : ∀ t ∈ Set.Ioo (0 : Real) b,
      ContMDiffAt 𝓘(Real, Real) I (2 : WithTop ℕ∞) γ t := by
    intro t ht
    exact hγInf.contMDiffAt.of_le (by norm_num)
  have hspeed : ∀ t ∈ Set.Ioo (0 : Real) b,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = ell ^ 2 := by
    intro t ht
    calc
      g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) =
          g.inner p u u := by
        simpa only [γ, curveVelocity] using
          intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t
      _ = ell ^ 2 := (Real.sq_sqrt hu.le).symm
  have hVdiff : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      DifferentiableAt Real (chartRepAt (I := I) γ (V i) t) t := by
    intro t ht i
    simpa only [γ, V] using
      (intrJacobi_diff (I := I) g hEnorm p u (v i) t).1
  have hDVdiff : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t := by
    intro t ht i
    simpa only [γ, V] using
      (intrJacobi_diff (I := I) g hEnorm p u (v i) t).2
  have hVperp : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
    intro t ht i
    simpa only [γ, V] using
      intrJacobi_perp_ne (I := I) g hEnorm p u (v i) ht.1.ne' (hperp i)
  have hDVperp : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0 := by
    intro t ht i
    simpa only [γ, V] using
      intrJacobi_dperp (I := I) g hEnorm p u (v i) ht.1.ne'
        (hperp i) (hVdiff t ht i)
  have hLI : ∀ t ∈ Set.Ioo (0 : Real) b,
      LinearIndependent Real fun i => V i t := by
    intro t ht
    simpa only [γ, V] using
      intrJacobi_li (I := I) g hEnorm p u v hv ht.1.ne' (hno t ht)
  have hW : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i j,
      jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
    intro t ht i j
    simpa only [γ, V] using
      intrWronsk_zero (I := I) g hEnorm p u (v i) (v j) b t
        ⟨ht.1.le, ht.2.le⟩
  have hJ : ∀ t ∈ Set.Ioo (0 : Real) b, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t := by
    intro t ht i
    simpa only [γ, V] using
      intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) t
  have hRatio : ∃ C : Real, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : Real),
        C ≤ curveDensity (I := I) g γ V t /
          hypDensity (q * ell) d t := by
    obtain ⟨C, hC, hraw⟩ :=
      radialRatio_auto (I := I) g p (u : E) (fun i => (v i : E))
        (q * ell) (mul_nonneg hq hell.le) hv
    have hcurve :
        ∀ᶠ t in 𝓝[>] (0 : Real),
          γ t = radialCurve (I := I) g p (u : E) t := by
      filter_upwards [intrJacobi_raw (I := I) g hEnorm p (u : E) (0 : E)]
        with t ht
      simpa only [γ] using ht.1
    have hfield_i : ∀ i,
        ∀ᶠ t in 𝓝[>] (0 : Real),
          (V i t : E) =
            (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) := by
      intro i
      filter_upwards [
        intrJacobi_raw (I := I) g hEnorm p (u : E) (v i : E)] with t ht
      simpa only [V] using ht.2
    have hfields :
        ∀ᶠ t in 𝓝[>] (0 : Real), ∀ i,
          (V i t : E) =
            (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) :=
      Filter.eventually_all.2 hfield_i
    refine ⟨C, hC, ?_⟩
    filter_upwards [hraw, hcurve, hfields] with t hrt hct hft
    have hgram :
        curveGram (I := I) g γ V t =
          curveGram (I := I) g
            (radialCurve (I := I) g p (u : E))
            (fun i => radialJacobiField (I := I) g p
              (u : E) (v i : E)) t := by
      ext i j
      simp only [curveGram, Matrix.of_apply]
      rw [hct, hft i, hft j]
    calc
      C ≤ curveDensity (I := I) g
            (radialCurve (I := I) g p (u : E))
            (fun i => radialJacobiField (I := I) g p
              (u : E) (v i : E)) t /
            hypDensity (q * ell) (Fintype.card (Fin d)) t := hrt
      _ = curveDensity (I := I) g γ V t /
            hypDensity (q * ell) d t := by
        rw [Fintype.card_fin]
        simp only [curveDensity, hgram]
  have hmean := curveMean_le_hyp
    (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V q ell b hq hell (Fintype.card_fin d) hd hγ hspeed
    hVperp hDVperp hVdiff hDVdiff hLI hW hJ hRic hRatio
  exact curveRatio_anti (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V (q * ell) b d (mul_nonneg hq hell.le) hγ hVdiff hLI hW hmean

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
