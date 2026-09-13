import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.DiskBoundary
import DifferentialGeometry.Geometry.Curvature.DiskRegularizer
import DifferentialGeometry.Geometry.Curvature.CurveReparametrization
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.AngleTrace
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Curvature.DiskSectionalDensity
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.WhitneyEmbedding

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

def diskLogPotential (kappa : ℂ → ℝ) (z : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * ∫ w in Metric.closedBall (0 : ℂ) 1,
    kappa w * (Real.log ‖z - w‖ + Real.log ‖1 - star w * z‖)


def diskBoundaryCurve : CurveMap ℂ := fun z _ => (diskBoundary z : ℂ)

theorem diskLogPotential_eq_diskRegularizerPotential (kappa : ℂ → ℝ)
    (hcompact : HasCompactSupport kappa) (hsmooth : ContDiff ℝ ∞ kappa)
    (hsupport : tsupport kappa ⊆ Metric.ball (0 : ℂ) 1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      diskLogPotential kappa z = DifferentialGeometry.Analysis.diskRegularizerPotential kappa z := by
  intro z hz
  obtain ⟨ρ, R, hρ, _hρ1, hR, hρR, hsρ⟩ :=
    DifferentialGeometry.Analysis.exists_disk_support_radii hcompact hsupport
  rw [DifferentialGeometry.Analysis.diskRegularizerPotential_eq_kernel_integral
    hcompact hsmooth hρ hρR hsρ (by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hR)]
  rw [diskLogPotential]
  have hset : (∫ w in Metric.closedBall (0 : ℂ) 1,
      kappa w * (Real.log ‖z - w‖ + Real.log ‖1 - star w * z‖))
      = ∫ w : ℂ, kappa w * (Real.log ‖z - w‖ + Real.log ‖1 - star w * z‖) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro w hw
    have hk : kappa w = 0 := by
      by_contra h
      exact hw (Metric.ball_subset_closedBall
        (hsupport (subset_tsupport kappa (Function.mem_support.mpr h))))
    simp only [hk, zero_mul]
  rw [hset]
  have hker : (∫ w : ℂ, kappa w * (Real.log ‖z - w‖ + Real.log ‖1 - star w * z‖)) =
      ∫ w : ℂ, kappa w * DifferentialGeometry.Analysis.diskNeumannLogKernel w z := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with w
    rw [DifferentialGeometry.Analysis.diskNeumannLogKernel]
    congr 2
  rw [hker]
  ring

theorem sectionalCurvature_complex_eq_planeGaussianCurvature
    (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) ℂ) (z : ℂ) :
    sectionalCurvature (I := 𝓘(ℝ, ℂ)) h z (1 : ℂ) Complex.I = planeGaussianCurvature h z := by
  erw [sectionalCurvature_eq_metricRm04StandardAt_div]
  rfl

private theorem diskBoundaryCurve_lift_eq_circleMap (x : ℝ) :
    diskBoundaryCurve.lift x 0 = circleMap 0 1 (2 * Real.pi * x) := by
  have h := diskBoundary_angle (2 * Real.pi * x)
  have hθ : 2 * Real.pi * x / (2 * Real.pi) = x := by
    field_simp
  rw [hθ] at h
  exact h

private theorem mfderiv_circleMap_eq_deriv (θ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (circleMap 0 1) θ (1 : ℝ) = deriv (circleMap 0 1) θ := by
  rw [mfderiv_eq_fderiv]
  exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := circleMap 0 1) (x := θ)

private theorem mfderiv_circleMap_one (θ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (circleMap 0 1) θ (1 : ℝ) =
      Complex.I * circleMap 0 1 θ := by
  rw [mfderiv_circleMap_eq_deriv, deriv_circleMap, mul_comm]

private theorem mfderiv_circleMap_ne_zero (θ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (circleMap 0 1) θ (1 : ℝ) ≠ 0 := by
  rw [mfderiv_circleMap_eq_deriv]
  exact deriv_circleMap_ne_zero (c := 0) (R := 1) (θ := θ) one_ne_zero

private theorem circleMap_one_norm (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  simp [circleMap]

private theorem sqrt_exp_two_mul (a : ℝ) : Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
  have h : Real.exp (2 * a) = Real.exp a ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h, Real.sqrt_sq (Real.exp_nonneg _)]

private theorem diskMapPartial_self (z v : ℂ) :
    diskMapPartial id z v = v := by
  rw [diskMapPartial]
  have h : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) id z = ContinuousLinearMap.id ℝ ℂ :=
    mfderiv_id
  rw [h]
  exact ContinuousLinearMap.id_apply v

private theorem circleMap_conformalCoefficient (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F) (z : ℂ) :
    diskMapConformalCoefficient (conformalEuclideanMetric F hF) id z = Real.exp (2 * F z) := by
  have hcoeff : diskMapConformalCoefficient (conformalEuclideanMetric F hF) id z =
      (conformalEuclideanMetric F hF).inner z (1 : ℂ) (1 : ℂ) := by
    rw [diskMapConformalCoefficient]
    congr 2 <;> exact diskMapPartial_self z _
  rw [hcoeff, conformalEuclideanMetric_inner]
  simp

private theorem circleMap_inwardConormal (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F) (z : ℂ) :
    diskMapInwardConormal (conformalEuclideanMetric F hF) id z = conformalCircleNormal F z := by
  rw [diskMapInwardConormal, conformalCircleNormal]
  rw [diskMapPartial_self, circleMap_conformalCoefficient F hF z, sqrt_exp_two_mul, Real.exp_neg]
  rfl

private theorem circleMap_conformalAt (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F) (z : ℂ) :
    DiskMapConformalAt (conformalEuclideanMetric F hF) id z := by
  have hpartial1 : diskMapPartial id z (1 : ℂ) = (1 : ℂ) := diskMapPartial_self z _
  have hpartialI : diskMapPartial id z Complex.I = Complex.I := diskMapPartial_self z _
  constructor
  · rw [hpartial1, hpartialI, conformalEuclideanMetric_inner]
    simp
  · rw [hpartial1, hpartialI, conformalEuclideanMetric_inner]
    simp

private theorem circleMap_fderiv_conformalCoefficient (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F) (z : ℂ) :
    (fderiv ℝ (diskMapConformalCoefficient (conformalEuclideanMetric F hF) id) z) z =
      2 * Real.exp (2 * F z) * fderiv ℝ F z z := by
  have hfun : diskMapConformalCoefficient (conformalEuclideanMetric F hF) id =
      fun w => Real.exp (2 * F w) := funext (circleMap_conformalCoefficient F hF)
  rw [hfun]
  have h : HasFDerivAt (fun w : ℂ => Real.exp (2 * F w))
      (Real.exp (2 * F z) • ((2 : ℝ) • fderiv ℝ F z)) z := by
    have h2 : HasFDerivAt (fun w : ℂ => 2 * F w) ((2 : ℝ) • fderiv ℝ F z) z :=
      (hF.differentiable (by simp) z).hasFDerivAt.const_mul 2
    exact h2.exp
  rw [h.fderiv]
  simp only [smul_apply]
  ring

private theorem diskBoundaryCurve_curvature_normal (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F) (x : ℝ) :
    let z := diskBoundaryCurve.lift x 0
    (conformalEuclideanMetric F hF).inner z
        (diskBoundaryCurve.curvatureVector (fun _ => conformalEuclideanMetric F hF) x 0)
        (-(Real.exp (-F z)) • z)
      = conformalCircleGeodesicCurvature F hF z := by
  dsimp only
  set z : ℂ := diskBoundaryCurve.lift x 0 with hzdef
  have hz : z = circleMap 0 1 (2 * Real.pi * x) :=
    hzdef.trans (diskBoundaryCurve_lift_eq_circleMap x)
  have hcurve : (fun s : ℝ => diskBoundaryCurve.lift s 0) =
      (circleMap 0 1) ∘ (fun s : ℝ => 2 * Real.pi * s) := by
    funext s
    exact diskBoundaryCurve_lift_eq_circleMap s
  have hφ : ContDiff ℝ ∞ (fun s : ℝ => 2 * Real.pi * s) := by fun_prop
  have hpos : 0 < deriv (fun s : ℝ => 2 * Real.pi * s) x := by
    have hd : deriv (fun s : ℝ => 2 * Real.pi * s) x = 2 * Real.pi := by
      have h := ((hasDerivAt_id x).const_mul (2 * Real.pi)).deriv
      rw [mul_one] at h
      exact h
    rw [hd]
    positivity
  have hreparam : riemannianCurveCurvature (conformalEuclideanMetric F hF)
      (fun s : ℝ => diskBoundaryCurve.lift s 0) x =
      riemannianCurveCurvature (conformalEuclideanMetric F hF) (circleMap 0 1)
        (2 * Real.pi * x) := by
    rw [hcurve]
    exact riemannianCurveCurvature_reparam_pos (conformalEuclideanMetric F hF)
      (contDiff_circleMap 0 1).contMDiff (fun t => mfderiv_circleMap_ne_zero t) hφ hpos
  have hdensity := diskMapBoundaryCurvature_density (conformalEuclideanMetric F hF)
    isOpen_univ contMDiffOn_id (by intro q _; exact Set.mem_univ q)
    (fun q _ => circleMap_conformalAt F hF q) (2 * Real.pi * x) (by
      rw [circleMap_conformalCoefficient F hF (circleMap 0 1 (2 * Real.pi * x))]
      exact Real.exp_pos _)
  dsimp only at hdensity
  simp only [Function.id_comp, id_eq] at hdensity
  rw [circleMap_inwardConormal F hF (circleMap 0 1 (2 * Real.pi * x)),
    circleMap_conformalCoefficient F hF (circleMap 0 1 (2 * Real.pi * x)),
    sqrt_exp_two_mul,
    circleMap_fderiv_conformalCoefficient F hF (circleMap 0 1 (2 * Real.pi * x))] at hdensity
  have hright : 1 + 2 * Real.exp (2 * F (circleMap 0 1 (2 * Real.pi * x))) *
        fderiv ℝ F (circleMap 0 1 (2 * Real.pi * x)) (circleMap 0 1 (2 * Real.pi * x)) /
        (2 * Real.exp (2 * F (circleMap 0 1 (2 * Real.pi * x)))) =
      1 + fderiv ℝ F (circleMap 0 1 (2 * Real.pi * x)) (circleMap 0 1 (2 * Real.pi * x)) := by
    have h2E : (2 : ℝ) * Real.exp (2 * F (circleMap 0 1 (2 * Real.pi * x))) ≠ 0 := by
      positivity
    field_simp [h2E]
  rw [hright] at hdensity
  have hdiv : (conformalEuclideanMetric F hF).inner (circleMap 0 1 (2 * Real.pi * x))
        (riemannianCurveCurvature (conformalEuclideanMetric F hF) (circleMap 0 1)
          (2 * Real.pi * x))
        (conformalCircleNormal F (circleMap 0 1 (2 * Real.pi * x))) =
      Real.exp (-F (circleMap 0 1 (2 * Real.pi * x))) *
        (1 + fderiv ℝ F (circleMap 0 1 (2 * Real.pi * x)) (circleMap 0 1 (2 * Real.pi * x))) := by
    have hE : Real.exp (F (circleMap 0 1 (2 * Real.pi * x))) ≠ 0 := Real.exp_ne_zero _
    rw [Real.exp_neg, ← div_eq_inv_mul, eq_div_iff hE]
    exact hdensity
  have hcurv : diskBoundaryCurve.curvatureVector (fun _ => conformalEuclideanMetric F hF) x 0 =
      riemannianCurveCurvature (conformalEuclideanMetric F hF) (circleMap 0 1)
        (2 * Real.pi * x) := by
    have h1 : diskBoundaryCurve.curvatureVector (fun _ => conformalEuclideanMetric F hF) x 0 =
        riemannianCurveCurvature (conformalEuclideanMetric F hF)
          (fun s : ℝ => diskBoundaryCurve.lift s 0) x := rfl
    rw [h1, hreparam]
  rw [hcurv, hz]
  rw [conformalCircleGeodesicCurvature_eq hF (circleMap_one_norm (2 * Real.pi * x))]
  simpa only [conformalCircleNormal] using hdiv

theorem geodesic_boundary_regularizer (kappa : ℂ → ℝ)
    (hsmooth : ContDiff ℝ ∞ kappa) (hnonneg : ∀ z, 0 ≤ kappa z)
    (hsupport : tsupport kappa ⊆ Metric.ball (0 : ℂ) 1)
    (hcompact : HasCompactSupport kappa)
    (hintegral : (∫ z in Metric.closedBall (0 : ℂ) 1, kappa z) = 2 * Real.pi) :
    ∃ f : ℂ → ℝ, ∃ h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) ℂ,
      ContDiff ℝ ∞ f ∧
      EqOn f (diskLogPotential kappa) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ z (v w : ℂ), h.inner z v w = Real.exp (2 * f z) * inner ℝ v w) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        sectionalCurvature (I := 𝓘(ℝ, ℂ)) h z (1 : ℂ) Complex.I * Real.exp (2 * f z) = kappa z) ∧
      ∀ x : ℝ,
        let z := diskBoundaryCurve.lift x 0
        h.inner z (diskBoundaryCurve.curvatureVector (fun _ => h) x 0)
          (-(Real.exp (-f z)) • z) * diskBoundaryCurve.speed (fun _ => h) x 0 = 0 := by
  have hmass : (∫ w : ℂ, kappa w) = 2 * Real.pi := by
    let _ := hnonneg
    have hset := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Metric.closedBall (0 : ℂ) 1) (f := kappa) (fun w hw => by
        by_contra h
        exact hw (Metric.ball_subset_closedBall
          (hsupport (subset_tsupport kappa (Function.mem_support.mpr h)))))
    exact hset.symm.trans hintegral
  obtain ⟨F, hF, heq, hcurv, hgeo⟩ :=
    exists_diskRegularizer_metric hcompact hsmooth hsupport hmass
  refine ⟨F, conformalEuclideanMetric F hF, hF, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [diskLogPotential_eq_diskRegularizerPotential kappa hcompact hsmooth hsupport z hz]
    exact (heq z hz).eq_of_nhds
  · intro z v w
    rw [conformalEuclideanMetric_inner]
  · intro z hz
    rw [sectionalCurvature_complex_eq_planeGaussianCurvature,
      ← tangentTwoJacobian_conformalPlane (f := F) hF z]
    exact hcurv z hz
  · intro x
    dsimp only
    rw [diskBoundaryCurve_curvature_normal F hF x]
    have hnorm : ‖diskBoundaryCurve.lift x 0‖ = 1 := by
      rw [diskBoundaryCurve_lift_eq_circleMap x]
      exact circleMap_one_norm (2 * Real.pi * x)
    rw [hgeo _ hnorm, zero_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]


def SmoothDisk.conformalFactor (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) : ℝ :=
  g.inner (u.map z) (u.differential z 1) (u.differential z 1)

def SmoothDisk.sectionalDensity (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) : ℝ :=
  if 0 < u.conformalFactor g z then
    sectionalCurvature (I := I) g (u.map z)
      (u.differential z 1) (u.differential z Complex.I) * u.conformalFactor g z
  else 0

def SmoothDisk.inwardConormal (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) : TangentSpace I (u.map z) :=
  if 0 < u.conformalFactor g z then
    -(Real.sqrt (u.conformalFactor g z))⁻¹ • u.differential z (z : ℂ)
  else 0


def SmoothDisk.boundarySpeed (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (x : ℝ) : ℝ :=
  let z := diskBoundary (x : Surgery.Topology.Circle)
  let V := u.differential z ((2 * Real.pi : ℝ) • (Complex.I * (z : ℂ)))
  Real.sqrt (g.inner (u.map z) V V)


def SmoothDisk.boundaryFluxDensity (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (V : ∀ z : Disk, TangentSpace I (u.map z)) (x : ℝ) : ℝ :=
    let z := diskBoundary (x : Surgery.Topology.Circle)
    g.inner (u.map z) (V z) (u.inwardConormal g z) * u.boundarySpeed g x


def SmoothDisk.boundaryFlux (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (V : ∀ z : Disk, TangentSpace I (u.map z)) : ℝ :=
  ∫ x in (0 : ℝ)..1, u.boundaryFluxDensity g V x

def SmoothDisk.boundaryCurvatureDensity (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta)) (x : ℝ) : ℝ := by
  let z := diskBoundary (x : Surgery.Topology.Circle)
  let c : CurveMap Q := fun theta _ => γ theta
  have V : TangentSpace I (u.map z) := by
    change TangentSpace I (u.map (diskBoundary (x : Surgery.Topology.Circle)))
    rw [htrace, sigma.lift_eq]
    exact c.curvatureVector (fun _ => g) (sigma.lift x) 0
  exact g.inner (u.map z) V (u.inwardConormal g z) * u.boundarySpeed g x

section SmoothExtension

variable [I.Boundaryless] [T2Space Q] [CompactSpace Q] [hne : Nonempty Q]

omit [CompleteSpace E] in
theorem SmoothDisk.exists_smoothExtension (u : SmoothDisk (I := I) (Q := Q)) :
    ∃ U : ℂ → Q, (∀ z : Disk, U z = u.map z) ∧
      ∃ N : Set ℂ, IsOpen N ∧ Metric.closedBall (0 : ℂ) 1 ⊆ N ∧
        ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U N := by
  classical
  obtain ⟨n, e, he, hemb, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := Q)
  obtain ⟨r, Ur, hUr, hrange, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he
      hemb.isEmbedding hi
  let ext : (z : Disk) → DiskLocalExtension (I := I) u.map z :=
    fun z => Classical.choice (u.smooth z)
  let Ucov : ℂ → Set ℂ := fun x =>
    if hx : x ∈ Metric.closedBall (0 : ℂ) 1 then (ext ⟨x, hx⟩).domain else Set.univ
  have hUcov : ∀ x ∈ Metric.closedBall (0 : ℂ) 1, Ucov x ∈ 𝓝 x := by
    intro x hx
    dsimp only [Ucov]
    rw [dif_pos hx]
    exact (ext ⟨x, hx⟩).isOpen_domain.mem_nhds (ext ⟨x, hx⟩).mem_domain
  obtain ⟨ι, f, hfsub⟩ :=
    SmoothBumpCovering.exists_isSubordinate (I := 𝓘(ℝ, ℂ)) (M := ℂ)
      (s := Metric.closedBall (0 : ℂ) 1) (U := Ucov) Metric.isClosed_closedBall hUcov
  let ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ (Metric.closedBall (0 : ℂ) 1) :=
    f.toSmoothPartitionOfUnity
  have hsub : ρ.IsSubordinate (fun i => Ucov (f.c i)) := hfsub.toSmoothPartitionOfUnity
  let Fl : ∀ i, DiskLocalExtension (I := I) u.map ⟨f.c i, f.c_mem' i⟩ :=
    fun i => ext ⟨f.c i, f.c_mem' i⟩
  let D : ι → Set ℂ := fun i => (Fl i).domain
  have hUci : ∀ i, Ucov (f.c i) = D i := by
    intro i
    dsimp only [Ucov, D, Fl]
    rw [dif_pos (f.c_mem' i)]
  have hsubD : ρ.IsSubordinate D := fun i => (hUci i) ▸ hsub i
  let g : ι → ℂ → EuclideanSpace ℝ (Fin n) :=
    fun i z => if z ∈ D i then e ((Fl i).map z) else 0
  have hg : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (g i) (D i) := by
    intro i
    have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun z => e ((Fl i).map z)) (D i) :=
      he.comp_contMDiffOn (Fl i).smooth
    refine hcomp.congr ?_
    intro z hz
    dsimp only [g]
    rw [if_pos hz]
  let V : ℂ → EuclideanSpace ℝ (Fin n) := fun z => ∑ᶠ i, ρ i z • g i z
  have hVsm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ V :=
    hsubD.contMDiff_finsum_smul (fun i => (Fl i).isOpen_domain) hg
  have hVeq : ∀ z (hz : z ∈ Metric.closedBall (0 : ℂ) 1),
      V z = e (u.map ⟨z, hz⟩) := by
    intro z hz
    have hfin : Function.HasFiniteSupport (fun i : ι => ρ i z) := ρ.locallyFinite.point_finite z
    have hterm : ∀ i, ρ i z • g i z = ρ i z • e (u.map ⟨z, hz⟩) := by
      intro i
      by_cases h : ρ i z = 0
      · rw [h, zero_smul, zero_smul]
      · have hmem : z ∈ D i :=
          hsubD i (subset_tsupport (ρ i) (Function.mem_support.mpr h))
        dsimp only [g]
        rw [if_pos hmem, ((Fl i).agrees ⟨hmem, hz⟩).trans (diskExtension_coe u.map ⟨z, hz⟩)]
    calc V z = ∑ᶠ i, ρ i z • g i z := rfl
      _ = ∑ᶠ i, ρ i z • e (u.map ⟨z, hz⟩) := finsum_congr hterm
      _ = (∑ᶠ i, ρ i z) • e (u.map ⟨z, hz⟩) := (finsum_smul' hfin _).symm
      _ = (1 : ℝ) • e (u.map ⟨z, hz⟩) := by rw [ρ.sum_eq_one hz]
      _ = e (u.map ⟨z, hz⟩) := one_smul ℝ _
  refine ⟨fun z => r (V z), ?_, V ⁻¹' Ur, hUr.preimage hVsm.continuous, ?_, ?_⟩
  · intro z
    change r (V (z : ℂ)) = u.map z
    rw [hVeq (z : ℂ) z.property, hleft]
  · intro z hz
    rw [Set.mem_preimage]
    exact hrange (hVeq z hz ▸ mem_range_self (u.map ⟨z, hz⟩))
  · exact hr.comp hVsm.contMDiffOn (fun z hz => hz)

end SmoothExtension

section StandardModelDensity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [CompleteSpace E] in
theorem SmoothDisk.exists_smoothDiskExtension (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := M)) :
    ∃ U : ℂ → M, DifferentialGeometry.Geometry.SmoothDiskExtension (E := E) u.map U := by
  obtain ⟨U, hU, N, hN, hsub, hsm⟩ :=
    SmoothDisk.exists_smoothExtension (I := 𝓘(ℝ, E)) (Q := M) (hne := ⟨u.map diskCenter⟩) u
  exact ⟨U, hU, N, hN, hsub, hsm⟩

omit [CompleteSpace E] [T2Space M] [CompactSpace M] in
theorem SmoothDisk.sectionalDensity_eq (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := M))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : DifferentialGeometry.Geometry.SmoothDiskExtension (E := E) u.map U)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    DifferentialGeometry.Geometry.diskMapSectionalDensity g U z =
      diskExtension (u.sectionalDensity g) z := by
  have hzcb : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
  have hUeq : U =ᶠ[𝓝 z] diskExtension u.map := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    rw [diskExtension_coe u.map ⟨w, Metric.ball_subset_closedBall hw⟩]
    exact hU.1 ⟨w, Metric.ball_subset_closedBall hw⟩
  have hUz : U z = diskExtension u.map z := hUeq.eq_of_nhds
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
      = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map) z := hUeq.mfderiv_eq
  have hwin : mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map)
        (Metric.closedBall (0 : ℂ) 1) z
      = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map) z :=
    mfderivWithin_of_mem_nhds
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)
  have hd1 : u.differential (⟨z, hzcb⟩ : Disk) (1 : ℂ) =
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map)
        (Metric.closedBall (0 : ℂ) 1) z (1 : ℂ) := rfl
  have hdI : u.differential (⟨z, hzcb⟩ : Disk) Complex.I =
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map)
        (Metric.closedBall (0 : ℂ) 1) z Complex.I := rfl
  simp only [DifferentialGeometry.Geometry.diskMapSectionalDensity,
    DifferentialGeometry.Geometry.diskMapConformalCoefficient,
    DifferentialGeometry.Geometry.diskMapPartial, SmoothDisk.sectionalDensity,
    SmoothDisk.conformalFactor, diskExtension, dif_pos hzcb]
  rw [hUz, hmf]
  simp only [← hwin, hd1, hdI]
  rw [← diskExtension_coe u.map ⟨z, hzcb⟩]
  by_cases hpos : 0 < g.inner (diskExtension u.map z)
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z (1 : ℂ))
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z (1 : ℂ))
  · rw [if_pos hpos]
  · rw [if_neg hpos]
    have hnn : 0 ≤ g.inner (diskExtension u.map z)
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z (1 : ℂ))
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z (1 : ℂ)) := by
      by_cases hv : mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u.map)
          (Metric.closedBall (0 : ℂ) 1) z (1 : ℂ) = 0
      · simp [hv]
      · exact (g.pos _ _ hv).le
    rw [le_antisymm (not_lt.mp hpos) hnn, mul_zero]

omit [CompleteSpace E] [T2Space M] [CompactSpace M] in
theorem SmoothDisk.sectionalDensity_ae_eq (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := M))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : DifferentialGeometry.Geometry.SmoothDiskExtension (E := E) u.map U) :
    (fun z => DifferentialGeometry.Geometry.diskMapSectionalDensity g U z) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) 1)]
      diskExtension (u.sectionalDensity g) := by
  filter_upwards [DifferentialGeometry.Geometry.ae_disk_interior] with z hz
  exact SmoothDisk.sectionalDensity_eq u g U hU hz

end StandardModelDensity

variable [hBoundary : I.Boundaryless] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
include hBoundary hT2 hCompact

def SmoothDisk.metricVariationDensity (u : SmoothDisk (I := I) (Q := Q))
    (g : ℝ → SmoothRiemannianMetric I Q) (J : Set ℝ) (t₀ : ℝ) (z : Disk) : ℝ :=
  if 0 < u.conformalFactor (g t₀) z then
    derivWithin (fun t => (g t).inner (u.map z) (u.differential z 1) (u.differential z 1)) J t₀ +
    derivWithin (fun t => (g t).inner (u.map z)
      (u.differential z Complex.I) (u.differential z Complex.I)) J t₀
  else 0

def SmoothDisk.isotopyVelocity (u : SmoothDisk (I := I) (Q := Q))
    (Phi : ℝ → Diffeomorph I I Q Q ∞) (J : Set ℝ) (t₀ : ℝ)
    (hid : ∀ q, Phi t₀ q = q) : ∀ z : Disk, TangentSpace I (u.map z) := by
  intro z
  simpa only [hid] using
    mfderivWithin 𝓘(ℝ, ℝ) I (fun t => Phi t (u.map z)) J t₀ 1


def SmoothDisk.transportedArea (u : SmoothDisk (I := I) (Q := Q))
    (g : ℝ → SmoothRiemannianMetric I Q) (Phi : ℝ → Diffeomorph I I Q Q ∞) (t : ℝ) : ℝ :=
  diskArea (g t) (fun z => Phi t (u.map z))

variable [SigmaCompactSpace Q] {D : RealTimeInterval} {a b : ℝ}

theorem rfs_plateau_upper_comparison (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (himm : ∀ t ∈ Icc a b, ∀ x, loopVelocity (I := I) (gamma t).toContinuousLoop x ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t₀).toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma t₀ (sigma.map theta))
    (hconformal : u.IsConformal (W.family.metric t₀))
    (hharmonic : u.IsHarmonic (W.family.metric t₀))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = gamma t₀ theta) →
        diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta) :
    let V := u.isotopyVelocity Phi (Icc a b) t₀ hid
    let metricTerm := u.metricVariationDensity W.family.metric (Icc a b) t₀
    let variation := (1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension metricTerm z) -
        u.boundaryFlux (W.family.metric t₀) V
    IntegrableOn (diskExtension metricTerm) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryFluxDensity (W.family.metric t₀) V) volume 0 1 ∧
      (∀ t ∈ Icc a b,
        loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t ≤
          u.transportedArea W.family.metric Phi t) ∧
      loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀ =
        u.transportedArea W.family.metric Phi t₀ ∧
      HasDerivWithinAt (u.transportedArea W.family.metric Phi) variation (Icc a b) t₀ ∧
      ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
        (loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) (t₀ + h) -
          loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀) / h ≤
            variation + epsilon := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
