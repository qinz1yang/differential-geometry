import DifferentialGeometry.Geometry.Exponential.BranchRadius
import DifferentialGeometry.Geometry.Exponential.EndpointShape
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Exponential.RawIntrinsicC2
import DifferentialGeometry.Geometry.Comparison.HessianAlongGeodesic
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiShape
import DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.LineSplit

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Laplacian of a selected branch radius

This file is the comparison-facing assembly for the fixed-first selected
inverse branch.  The first checked brick records that the branch radius has
zero second derivative along every positive intrinsic radial ray that remains
in the selected branch.
-/

noncomputable section

open Bundle Filter Function Manifold Tensor0SBundle
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Exponential
open Variation
open VolumeComparison
open CovariantDerivativeAlong
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

/-- The selected branch radius restricts to an affine function on a positive
intrinsic radial ray, so its ordinary second derivative there vanishes. -/
theorem branchDeriv2_zero
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M}
    (B : ExpInvBranch (I := I) g hEnorm p)
    {x : TangentSpace I p} {t : Real}
    (ht : 0 < t)
    (hsrc : t • (x : E) ∈ B.hom.source) :
    (deriv^[2]
      (fun s : Real =>
        branchRadius (I := I) g B
          (intrinsicGeodesic (I := I) g hEnorm p x s))) t = 0 := by
  let f : Real → Real := fun s =>
    branchRadius (I := I) g B
      (intrinsicGeodesic (I := I) g hEnorm p x s)
  let a : Real := Real.sqrt (g.inner p x x)
  let ℓ : Real → Real := fun s => s * a
  have hray : f =ᶠ[𝓝 t] ℓ := by
    simpa only [f, ℓ, a] using
      branchRadius_ray (I := I) B ht hsrc
  calc
    (deriv^[2] f) t = (deriv^[2] ℓ) t :=
      Filter.EventuallyEq.deriv_eq hray.deriv
    _ = 0 := by
      change deriv (deriv ℓ) t = 0
      have hfirst : deriv ℓ = fun _ : Real => a := by
        funext s
        simpa only [ℓ, id_eq, one_mul] using
          ((hasDerivAt_id s).mul_const a).deriv
      rw [hfirst, deriv_const]

/-- The Hessian of the selected branch radius vanishes on the terminal radial
velocity of its time-one intrinsic geodesic. -/
theorem branchHess_radial
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M}
    (B : ExpInvBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : (u : E) ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    let γ : Real → M :=
      intrinsicGeodesic (I := I) g hEnorm p u
    hessFun (I := I) g
        (branchRadius (I := I) g B)
        (γ 1) (curveVelocity (I := I) γ 1)
        (curveVelocity (I := I) γ 1) = 0 := by
  dsimp only
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨U, hUopen, hqU, hrU⟩ :=
    branchRadius_open (I := I) B hu hu_pos
  have hγ : ContMDiff 𝓘(Real, Real) I ∞ γ := by
    apply contMDiffOn_univ.mp
    refine Geodesic.isGeodesicOn_contMDiffOn_infty
      (I := I) g isOpen_univ ?_ ?_
    · exact
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u).isGeodesicOn
          Set.univ
    · exact
        (intrinsicGeodesic_continuous (I := I) g hEnorm p u).continuousOn
  have hgeo : Geodesic.IsGeodesic (I := I) g γ := by
    simpa only [γ] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
  have hqU' : γ 1 ∈ U := by
    simpa only [γ, expMapIntrinsic_def] using hqU
  have htrace :=
    deriv2_comp_geo_on (I := I) g hUopen hrU hγ hgeo hqU'
  have hu1 :
      (1 : Real) • (u : E) ∈ B.hom.source := by
    simpa only [one_smul] using hu
  have hzero :
      (deriv^[2]
        (branchRadius (I := I) g B ∘ γ)) 1 = 0 := by
    simpa only [γ, Function.comp_apply, one_smul] using
      branchDeriv2_zero (I := I) B (t := (1 : Real)) zero_lt_one hu1
  rw [htrace] at hzero
  simpa only [curveVelocity] using hzero

/-- The scalar Laplacian of the fixed-first branch radius at a time-one
intrinsic endpoint is the transverse Jacobi mean curvature divided by the
launch speed. -/
theorem branchLap_eq_mean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {p : M}
    (B : ExpInvBranch (I := I) g hEnorm p)
    (u : TangentSpace I p)
    (v : ι → TangentSpace I p)
    (hu : (u : E) ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u)
    (hv : LinearIndependent Real v)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hcard :
      Fintype.card ι = Module.finrank Real E - 1) :
    let γ : Real → M :=
      intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i =>
      intrinsicJacobi (I := I) g hEnorm p u (v i)
    laplacian (I := I) (LeviCivita (I := I) g) g
        (branchRadius (I := I) g B) (γ 1)
      =
        curveMean (I := I) g γ V 1 /
          Real.sqrt (g.inner p u u) := by
  classical
  dsimp only
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p u
  let V := fun i =>
    intrinsicJacobi (I := I) g hEnorm p u (v i)
  let q : M := γ 1
  let Z : TangentSpace I q := curveVelocity (I := I) γ 1
  let Hess :
      Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 q :=
    hessTensorAt (I := I) g (branchRadius (I := I) g B) q
  obtain ⟨U, hUopen, hqU, hrU⟩ :=
    branchRadius_open (I := I) B hu hu_pos
  have hqU' : q ∈ U := by
    simpa only [q, γ, expMapIntrinsic_def] using hqU
  have hZ : 0 < g.inner q Z Z := by
    rw [show g.inner q Z Z = g.inner p u u by
      simpa only [q, Z, γ, curveVelocity] using
        intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u 1]
    exact hu_pos
  have hperp_end : ∀ i, g.inner q Z (V i 1) = 0 := by
    intro i
    have hp :
        g.inner q Z (V i 1) = g.inner p u (v i) := by
      simpa only [q, Z, γ, V, curveVelocity, intrinsicVelocityLift] using
        intrinsicJacobi_perp (I := I) g hEnorm p u (v i)
    exact hp.trans (hperp i)
  have hLI : LinearIndependent Real fun i => V i 1 := by
    simpa only [V] using intrinsicJacobi_li (I := I) B hu v hv
  have hsplit :=
    trace_eq_line_add (I := I) g Z (fun i => V i 1) Hess
      hZ hperp_end hLI hcard
  have hradial : Hess (vec2 (I := I) Z Z) = 0 := by
    rw [hessTensorAt_apply]
    simpa only [q, Z, γ] using
      branchHess_radial (I := I) B hu hu_pos
  let G : Matrix ι ι Real :=
    Matrix.of fun i j => g.inner q (V i 1) (V j 1)
  let A : Matrix ι ι Real :=
    Matrix.of fun i j => Hess (vec2 (I := I) (V i 1) (V j 1))
  have hA :
      A =
        (Real.sqrt (g.inner p u u))⁻¹ •
          curveMixedGram (I := I) g γ V 1 := by
    ext i j
    simp only [A, Hess, Matrix.smul_apply, curveMixedGram, Matrix.of_apply,
      hessTensorAt_apply]
    rw [branchHess_shape (I := I) B hu hu_pos (hperp i) (hperp j)]
    simp only [γ, V, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  have hmean :
      Matrix.trace (G⁻¹ * A) =
        curveMean (I := I) g γ V 1 /
          Real.sqrt (g.inner p u u) := by
    rw [hA, Matrix.mul_smul, Matrix.trace_smul]
    simp only [smul_eq_mul, curveMean, curveShape, div_eq_mul_inv]
    change
      (Real.sqrt (g.inner p u u))⁻¹ *
          Matrix.trace
            ((curveGram (I := I) g γ V 1)⁻¹ *
              curveMixedGram (I := I) g γ V 1) =
        Matrix.trace
            ((curveGram (I := I) g γ V 1)⁻¹ *
              curveMixedGram (I := I) g γ V 1) *
          (Real.sqrt (g.inner p u u))⁻¹
    ring
  have hlap :=
    lap_eq_hess_on (I := I) g hUopen hrU hqU'
  rw [hlap]
  change metricTracePair0SAt (I := I) g Hess = _
  simpa only [G, A, hradial, mul_zero, zero_add, hmean] using hsplit

private theorem smul_c2_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {t : Real}
    (htx : ‖t • x‖ < expMapC2Radius (I := I) g p) :
    ∀ᶠ s in 𝓝 t, ‖s • x‖ < expMapC2Radius (I := I) g p := by
  have hmap : Continuous fun s : Real => s • x :=
    continuous_id.smul continuous_const
  have hmem :
      t • x ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := by
    simpa only [Metric.mem_ball, dist_zero_right] using htx
  have hev :=
    hmap.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hmem)
  simpa only [Metric.mem_ball, dist_zero_right] using hev

private lemma metric_smul_left
    (g : SmoothRiemannianMetric I M) (p : M)
    (c : Real) (v y : E) :
    g.inner p
        (show TangentSpace I p from c • v)
        (show TangentSpace I p from y) =
      c * g.inner p
        (show TangentSpace I p from v)
        (show TangentSpace I p from y) := by
  change
    g.inner p
        (c • (show TangentSpace I p from v))
        (show TangentSpace I p from y) =
      _
  rw [map_smul (g.inner p), ContinuousLinearMap.smul_apply, smul_eq_mul]

private lemma metric_smul_right
    (g : SmoothRiemannianMetric I M) (p : M)
    (c : Real) (v y : E) :
    g.inner p
        (show TangentSpace I p from v)
        (show TangentSpace I p from c • y) =
      c * g.inner p
        (show TangentSpace I p from v)
        (show TangentSpace I p from y) := by
  change
    g.inner p
        (show TangentSpace I p from v)
        (c • (show TangentSpace I p from y)) =
      _
  rw [map_smul (g.inner p (show TangentSpace I p from v)), smul_eq_mul]

private theorem radialCurve_eq_intr
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (x : E) {t : Real}
    (htx : ‖t • x‖ < expMapC2Radius (I := I) g p) :
    radialCurve (I := I) g p x =ᶠ[𝓝 t]
      intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x) := by
  filter_upwards [smul_c2_eventually (I := I) g p x htx] with s hs
  rw [radialCurve, exp_eq_intr_of_c2 (I := I) g hEnorm p hs]
  simpa only [expMapIntrinsic_def] using
    intrinsicGeodesic_smul (I := I) g hEnorm p
      (show TangentSpace I p from x) s

private theorem radialJacobi_eq_intr
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (x w : E) {t : Real}
    (htx : ‖t • x‖ < expMapC2Radius (I := I) g p) :
    ∀ᶠ s in 𝓝 t,
      (radialJacobiField (I := I) g p x w s : E) =
        intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from x)
          (show TangentSpace I p from w) s := by
  filter_upwards [smul_c2_eventually (I := I) g p x htx] with s hs
  have hparam :
      Tendsto (fun r : Real => s • (x + r • w))
        (𝓝 (0 : Real)) (𝓝 (s • x)) := by
    have hcont : ContinuousAt (fun r : Real => s • (x + r • w)) 0 :=
      continuousAt_const.smul
        (continuousAt_const.add (continuousAt_id.smul continuousAt_const))
    simpa only [ContinuousAt, zero_smul, add_zero] using hcont
  have hraw :
      (fun r : Real =>
        expMap (I := I) g p
          (show TangentSpace I p from s • (x + r • w))) =ᶠ[𝓝 (0 : Real)]
        fun r : Real =>
          expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from s • (x + r • w)) :=
    hparam.eventually (exp_germ_eq_intr (I := I) g hEnorm p hs)
  have hscale :
      (fun r : Real =>
        expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from s • (x + r • w))) =
        fun r : Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + r • w) s := by
    funext r
    simpa only [expMapIntrinsic_def] using
      intrinsicGeodesic_smul (I := I) g hEnorm p
        (show TangentSpace I p from x + r • w) s
  have hagree :
      (fun r : Real =>
        expMap (I := I) g p
          (show TangentSpace I p from s • (x + r • w))) =ᶠ[𝓝 (0 : Real)]
        fun r : Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + r • w) s := by
    exact hraw.trans (Filter.Eventually.of_forall (fun r => congrFun hscale r))
  have hmf :=
    Filter.EventuallyEq.mfderiv_eq
      (I := 𝓘(Real, Real)) (I' := I) hagree
  have happ := congrArg (fun L => (L (1 : Real) : E)) hmf
  simpa only [radialJacobiField, intrinsicJacobi] using happ

private theorem intrJacobi_smul
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (x w : E) (t s : Real) :
    (intrinsicJacobi (I := I) g hEnorm p
        (show TangentSpace I p from t • x)
        (show TangentSpace I p from t • w) s : E) =
      intrinsicJacobi (I := I) g hEnorm p
        (show TangentSpace I p from x)
        (show TangentSpace I p from w) (t * s) := by
  have hfun :
      (fun r : Real =>
        intrinsicGeodesic (I := I) g hEnorm p
          ((show TangentSpace I p from t • x) +
            r • (show TangentSpace I p from t • w)) s) =
        fun r : Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            ((show TangentSpace I p from x) +
              r • (show TangentSpace I p from w)) (t * s) := by
    funext r
    have hvec :
        (show TangentSpace I p from t • x) +
            r • (show TangentSpace I p from t • w) =
          (show TangentSpace I p from t • (x + r • w)) := by
      change (t • x) + r • (t • w) = t • (x + r • w)
      module
    rw [hvec]
    calc
      intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from t • (x + r • w)) s =
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from s • (t • (x + r • w))) 1 := by
              symm
              exact intrinsicGeodesic_smul (I := I) g hEnorm p
                (show TangentSpace I p from t • (x + r • w)) s
      _ = intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from (t * s) • (x + r • w)) 1 := by
              rw [show s • (t • (x + r • w)) =
                (t * s) • (x + r • w) by module]
      _ = intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + r • w) (t * s) := by
              exact intrinsicGeodesic_smul (I := I) g hEnorm p
                (show TangentSpace I p from x + r • w) (t * s)
  unfold intrinsicJacobi
  rw [hfun]
  rfl

/-- The scalar Laplacian of the selected branch radius along the chart-fixed
raw radial family is the raw transverse Jacobi mean divided by the unscaled
launch speed. -/
theorem radialLap_eq_mean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {p : M}
    (B : ExpInvBranch (I := I) g hEnorm p)
    (x : E) (v : ι → E) (t : Real)
    (ht : 0 < t)
    (hx_pos : 0 < g.inner p x x)
    (hsrc : t • x ∈ B.hom.source)
    (hC2 :
      ‖t • x‖ < expMapC2Radius (I := I) g p)
    (hv : LinearIndependent Real v)
    (hperp : ∀ i, g.inner p x (v i) = 0)
    (hcard :
      Fintype.card ι = Module.finrank Real E - 1) :
    let γ := radialCurve (I := I) g p x
    let V := fun i =>
      radialJacobiField (I := I) g p x (v i)
    laplacian (I := I) (LeviCivita (I := I) g) g
        (branchRadius (I := I) g B) (γ t)
      =
        curveMean (I := I) g γ V t /
          Real.sqrt (g.inner p x x) := by
  classical
  dsimp only
  let γR : Real → M := radialCurve (I := I) g p x
  let VR := fun i => radialJacobiField (I := I) g p x (v i)
  let γI : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from x)
  let VI := fun i =>
    intrinsicJacobi (I := I) g hEnorm p
      (show TangentSpace I p from x)
      (show TangentSpace I p from v i)
  let γT : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from t • x)
  let VT := fun i =>
    intrinsicJacobi (I := I) g hEnorm p
      (show TangentSpace I p from t • x)
      (show TangentSpace I p from t • v i)
  have hγRI : γR =ᶠ[𝓝 t] γI := by
    simpa only [γR, γI] using
      radialCurve_eq_intr (I := I) g hEnorm p x hC2
  have hVRI (i : ι) :
      ∀ᶠ s in 𝓝 t, (VR i s : E) = (VI i s : E) := by
    simpa only [VR, VI] using
      radialJacobi_eq_intr (I := I) g hEnorm p x (v i) hC2
  have hGramRI :
      curveGram (I := I) g γR VR t =
        curveGram (I := I) g γI VI t := by
    ext i j
    simp only [curveGram, Matrix.of_apply]
    have hγt := hγRI.eq_of_nhds
    have hVi := Filter.EventuallyEq.eq_of_nhds (hVRI i)
    have hVj := Filter.EventuallyEq.eq_of_nhds (hVRI j)
    rw [hγt]
    exact congrArg₂ (fun a b : E => g.inner (γI t) a b) hVi hVj
  have hMixedRI :
      curveMixedGram (I := I) g γR VR t =
        curveMixedGram (I := I) g γI VI t := by
    ext i j
    simp only [curveMixedGram, Matrix.of_apply]
    have hγt := hγRI.eq_of_nhds
    have hVj := Filter.EventuallyEq.eq_of_nhds (hVRI j)
    have hDi :=
      covDerivAlong_congr_curve (I := I) g (VR i) (VI i)
        hγRI (hVRI i)
    rw [hγt]
    exact congrArg₂ (fun a b : E => g.inner (γI t) a b) hDi hVj
  have hMeanRI :
      curveMean (I := I) g γR VR t =
        curveMean (I := I) g γI VI t := by
    rw [curveMean, curveMean, curveShape, curveShape, hGramRI, hMixedRI]
  have hγT (s : Real) : γT s = γI (t * s) := by
    dsimp only [γT, γI]
    calc
      intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from t • x) s =
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from s • (t • x)) 1 := by
              symm
              exact intrinsicGeodesic_smul (I := I) g hEnorm p
                (show TangentSpace I p from t • x) s
      _ = intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from (t * s) • x) 1 := by
              rw [show s • (t • x) = (t * s) • x by module]
      _ = intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x) (t * s) := by
              exact intrinsicGeodesic_smul (I := I) g hEnorm p
                (show TangentSpace I p from x) (t * s)
  have hVT (i : ι) (s : Real) :
      (VT i s : E) = (VI i (t * s) : E) := by
    simpa only [VT, VI] using
      intrJacobi_smul (I := I) g hEnorm p x (v i) t s
  have hGramT :
      curveGram (I := I) g γT VT 1 =
        curveGram (I := I) g γI VI t := by
    ext i j
    simp only [curveGram, Matrix.of_apply]
    rw [hγT, hVT, hVT, mul_one]
  have hDerivT (i : ι) :
      (covDerivAlong (I := I) g γT (VT i) 1 : E) =
        t • covDerivAlong (I := I) g γI (VI i) t := by
    have hγfun : γT = fun s => γI (t * s) := funext hγT
    have hVfun : VT i = fun s => VI i (t * s) := by
      funext s
      exact hVT i s
    rw [hγfun, hVfun]
    have hscale :=
      covDeriv_comp_mul (I := I) g γI (VI i) t 1
    rw [mul_one] at hscale
    exact hscale
  have hMixedT :
      curveMixedGram (I := I) g γT VT 1 =
        t • curveMixedGram (I := I) g γI VI t := by
    ext i j
    simp only [curveMixedGram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hγT, hVT, mul_one]
    have hDi := hDerivT i
    change
      g.inner (γI t)
          (covDerivAlong (I := I) g γT (VT i) 1)
          (VI j t) =
        t * g.inner (γI t)
          (covDerivAlong (I := I) g γI (VI i) t)
          (VI j t)
    rw [hDi, (g.inner (γI t)).map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hMeanT :
      curveMean (I := I) g γT VT 1 =
        t * curveMean (I := I) g γI VI t := by
    rw [curveMean, curveMean, curveShape, curveShape, hGramT, hMixedT,
      Matrix.mul_smul, Matrix.trace_smul]
    simp only [smul_eq_mul]
  have hu_pos :
      0 < g.inner p (t • x) (t • x) := by
    have hinner :
        g.inner p (t • x) (t • x) =
          t * (t * g.inner p x x) := by
      rw [metric_smul_left (I := I) g p t x (t • x),
        metric_smul_right (I := I) g p t x x]
    rw [hinner]
    exact mul_pos ht (mul_pos ht hx_pos)
  have hvT : LinearIndependent Real fun i => t • v i := by
    let ut : Realˣ := Units.mk0 t ht.ne'
    have hunit := hv.units_smul (fun _ => ut)
    change LinearIndependent Real (fun i => (ut : Real) • v i) at hunit
    simpa only [ut, Units.val_mk0] using hunit
  have hperpT : ∀ i, g.inner p (t • x) (t • v i) = 0 := by
    intro i
    rw [metric_smul_left (I := I) g p t x (t • v i),
      metric_smul_right (I := I) g p t x (v i),
      hperp i, mul_zero, mul_zero]
  have hbranch :
      laplacian (I := I) (LeviCivita (I := I) g) g
          (branchRadius (I := I) g B) (γT 1)
        =
          curveMean (I := I) g γT VT 1 /
            Real.sqrt (g.inner p (t • x) (t • x)) := by
    simpa only [γT, VT] using
      branchLap_eq_mean (I := I) g hEnorm B
        (show TangentSpace I p from t • x)
        (fun i => show TangentSpace I p from t • v i)
        hsrc hu_pos hvT hperpT hcard
  have hend : γR t = γT 1 := by
    dsimp only [γR, γT]
    simpa only [radialCurve, expMapIntrinsic_def] using
      exp_eq_intr_of_c2 (I := I) g hEnorm p hC2
  have hinnerT :
      g.inner p (t • x) (t • x) =
        t ^ 2 * g.inner p x x := by
    rw [metric_smul_left (I := I) g p t x (t • x),
      metric_smul_right (I := I) g p t x x]
    ring
  have hsqrt :
      Real.sqrt (g.inner p (t • x) (t • x)) =
        t * Real.sqrt (g.inner p x x) := by
    rw [hinnerT, Real.sqrt_mul (sq_nonneg t),
      Real.sqrt_sq_eq_abs, abs_of_pos ht]
  change
    laplacian (I := I) (LeviCivita (I := I) g) g
        (branchRadius (I := I) g B) (γR t) =
      curveMean (I := I) g γR VR t /
        Real.sqrt (g.inner p x x)
  rw [hend, hbranch, hMeanT, ← hMeanRI, hsqrt]
  field_simp [ht.ne', (Real.sqrt_pos.2 hx_pos).ne']

end Riemannian
end Geometry
end DifferentialGeometry
