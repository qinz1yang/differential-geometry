import DifferentialGeometry.Geometry.Exponential.BranchRadius
import DifferentialGeometry.Geometry.Exponential.IntrinsicGauss
import DifferentialGeometry.Geometry.Exponential.JacobiVariation
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule

set_option autoImplicit false

/-!
# Endpoint Jacobi fields for selected exponential branches

This file names the intrinsic initial-velocity Jacobi field and records that a
selected fixed-first inverse branch preserves linear independence at time one.
The second-order endpoint shape identity will be built on this API.
-/

noncomputable section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The intrinsic Jacobi field obtained by varying the initial velocity along
the affine line `u + r • w`. -/
noncomputable def intrinsicJacobi
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u w : TangentSpace I p) (s : Real) :
    TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p u s) :=
  mfderiv 𝓘(Real, Real) I
    (fun r : Real =>
      intrinsicGeodesic (I := I) g hEnorm p (u + r • w) s)
    0 1

/-- Pairing an endpoint Jacobi field with the terminal radial velocity recovers
the corresponding launch pairing. -/
theorem intrinsicJacobi_perp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
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

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
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

/-- The covariant derivative of the terminal unit radial velocity under an
affine change of initial velocity is the terminal Jacobi derivative, together
with the derivative of the normalizing launch length. -/
theorem endpointJacobi_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
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
        (I := I) g F hF 1
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

/-- The Hessian of the selected fixed-first branch radius at a time-one
intrinsic endpoint is the normalized endpoint Jacobi derivative, with the
rank-one correction coming from differentiating the launch length. -/
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
  rw [hpair]
  have hroot_ne : Real.sqrt (g.inner p u u) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_pos)
  field_simp [hroot_ne]
  rfl

/-- For launch directions perpendicular to the radial direction, the
rank-one normalization correction in `branchHess_jacobi` vanishes. -/
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

/-- A selected fixed-first inverse branch carries a linearly independent
initial family to a linearly independent family of endpoint Jacobi fields. -/
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
