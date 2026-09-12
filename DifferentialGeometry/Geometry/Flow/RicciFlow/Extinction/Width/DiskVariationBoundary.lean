import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge
import DifferentialGeometry.Geometry.Curvature.DiskTraceDensity
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

theorem SmoothWeaklyMonotoneCircleMap.exists_angle_parameter
    (sigma : SmoothWeaklyMonotoneCircleMap) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ Monotone φ ∧
      (∀ θ, φ (θ + 2 * Real.pi) = φ θ + 1) ∧
      (∀ θ, (φ θ : Surgery.Topology.Circle) =
        sigma.map ((θ / (2 * Real.pi) : ℝ) : Surgery.Topology.Circle)) := by
  refine ⟨fun θ => sigma.lift (θ / (2 * Real.pi)),
    sigma.smooth_lift.comp (contDiff_id.div_const _), ?_, ?_, ?_⟩
  · intro a b hab
    exact sigma.monotone_lift (div_le_div_of_nonneg_right hab (by positivity))
  · intro θ
    have hθ : (θ + 2 * Real.pi) / (2 * Real.pi) = θ / (2 * Real.pi) + 1 := by
      field_simp
    dsimp only
    rw [hθ, sigma.increment]
  · intro θ
    exact (sigma.lift_eq (θ / (2 * Real.pi))).symm.trans (congrArg (fun r : ℝ =>
      sigma.map (r : Surgery.Topology.Circle)) (by ring))

theorem CurveMap.curvatureVector_loop_eq_riemannianCurveCurvature
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    CurveMap.curvatureVector (fun θ _ => γ θ) (fun _ => g) x t =
      riemannianCurveCurvature g (fun y => γ (y : Surgery.Topology.Circle)) x := rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
private theorem diskMapPartial_smul (U : ℂ → Q) (z : ℂ) (w : ℂ) (a : ℝ) :
    diskMapPartial (E := E) (M := Q) U z (a • w) =
      a • diskMapPartial (E := E) (M := Q) U z w := by
  rw [diskMapPartial, diskMapPartial]
  exact map_smul (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) a w

omit [FiniteDimensional ℝ E] in
private theorem inner_smul_sq (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (p : Q)
    (v : TangentSpace 𝓘(ℝ, E) p) (a : ℝ) :
    g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v := by
  rw [map_smul (g.inner p), smul_apply, smul_eq_mul,
    map_smul (g.inner p v), smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
theorem SmoothDisk.boundarySpeed_eq_diskMapConformalCoefficient
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U) (x : ℝ)
    (hconf : DiskMapConformalAt g U (circleMap 0 1 (2 * Real.pi * x))) :
    u.boundarySpeed g x = 2 * Real.pi *
      Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 (2 * Real.pi * x))) := by
  simp only [SmoothDisk.boundarySpeed]
  set z : Disk := diskBoundary (x : Surgery.Topology.Circle) with hzdef
  have hz : (z : ℂ) = circleMap 0 1 (2 * Real.pi * x) := by
    have h := diskBoundary_angle (2 * Real.pi * x)
    have hθ : 2 * Real.pi * x / (2 * Real.pi) = x := by field_simp
    rw [hθ] at h
    exact h
  have hnorm : ‖(z : ℂ)‖ = 1 := by
    rw [hz, circleMap]
    simp [Complex.norm_exp]
  have hd (w : ℂ) : (u.differential z w : E) = (diskMapPartial (M := Q) U z w : E) :=
    SmoothDisk.differential_eq_diskMapPartial u hU z w
  have hpoint : u.map z = U z := (hU.1 z).symm
  have hconfz : DiskMapConformalAt g U (z : ℂ) := by rw [hz]; exact hconf
  have hinner : g.inner (U z) (diskMapPartial (M := Q) U z (Complex.I * (z : ℂ)))
      (diskMapPartial (M := Q) U z (Complex.I * (z : ℂ))) =
      diskMapConformalCoefficient g U (z : ℂ) := by
    rw [hconfz.inner_partials, diskMapConformalCoefficient]
    have h1 : inner ℝ (Complex.I * (z : ℂ)) (Complex.I * (z : ℂ)) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_mul, Complex.norm_I, one_mul, hnorm, one_pow]
    rw [h1, mul_one]
  have hsmul : diskMapPartial (M := Q) U z ((2 * Real.pi : ℝ) • (Complex.I * (z : ℂ))) =
      (2 * Real.pi : ℝ) • diskMapPartial (M := Q) U z (Complex.I * (z : ℂ)) :=
    diskMapPartial_smul (E := E) U z _ _
  rw [hpoint, hd ((2 * Real.pi : ℝ) • (Complex.I * (z : ℂ))), hsmul,
    inner_smul_sq g (U z) (diskMapPartial (M := Q) U z (Complex.I * (z : ℂ))) (2 * Real.pi),
    hinner, hz]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ 2),
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

omit [FiniteDimensional ℝ E] in
theorem SmoothDisk.inwardConormal_eq_diskMapInwardConormal
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U) (z : Disk) :
    (u.inwardConormal g z : E) = (diskMapInwardConormal g U (z : ℂ) : E) := by
  have hpt : U (z : ℂ) = u.map z := hU.1 z
  have hd (v : ℂ) : (u.differential z v : E) = (diskMapPartial (M := Q) U z v : E) :=
    SmoothDisk.differential_eq_diskMapPartial u hU z v
  have hcoeff' : diskMapConformalCoefficient g U (z : ℂ) = u.conformalFactor g z := by
    rw [diskMapConformalCoefficient, SmoothDisk.conformalFactor, hpt, ← hd 1]
  have hcoeff : u.conformalFactor g z = diskMapConformalCoefficient g U (z : ℂ) := hcoeff'.symm
  rw [SmoothDisk.inwardConormal, diskMapInwardConormal, hcoeff]
  by_cases h : 0 < diskMapConformalCoefficient g U (z : ℂ)
  · rw [if_pos h, ← hd (z : ℂ)]
    rfl
  · rw [if_neg h]
    have hnn := diskMapConformalCoefficient_nonneg g U (z : ℂ)
    have hzero : diskMapConformalCoefficient g U (z : ℂ) = 0 := le_antisymm (not_lt.mp h) hnn
    rw [hzero, Real.sqrt_zero, inv_zero, neg_zero, zero_smul]
    rfl

theorem SmoothDisk.boundaryCurvatureDensity_eq_diskMapTraceBoundaryDensity
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (γ : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta))
    (hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U z) (x : ℝ) :
    u.boundaryCurvatureDensity g γ sigma htrace x =
      2 * Real.pi * diskMapTraceBoundaryDensity g U
        (fun t : ℝ => γ (t : Surgery.Topology.Circle))
        (fun θ => sigma.lift (θ / (2 * Real.pi))) (2 * Real.pi * x) := by
  have hbc : u.boundaryCurvatureDensity g γ sigma htrace x =
      g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (CurveMap.curvatureVector (fun theta _ => γ.toContinuousLoop theta) (fun _ => g)
          (sigma.lift x) 0)
        (u.inwardConormal g (diskBoundary (x : Surgery.Topology.Circle))) *
        u.boundarySpeed g x := rfl
  rw [hbc]
  set z : Disk := diskBoundary (x : Surgery.Topology.Circle) with hzdef
  have hz : (z : ℂ) = circleMap 0 1 (2 * Real.pi * x) := by
    have h := diskBoundary_angle (2 * Real.pi * x)
    have hθ : 2 * Real.pi * x / (2 * Real.pi) = x := by field_simp
    rw [hθ] at h
    exact h
  have hzmem : (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [hz]
    simp [circleMap, Metric.mem_closedBall, Complex.norm_exp, Complex.mul_re]
  have hφ : (2 * Real.pi * x) / (2 * Real.pi) = x :=
    mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi) ≠ 0)
  have hpoint : U (z : ℂ) = u.map z := hU.1 z
  have hcurve : CurveMap.curvatureVector (fun theta _ => γ.toContinuousLoop theta) (fun _ => g)
      (sigma.lift x) 0 =
      riemannianCurveCurvature g (fun t : ℝ => γ (t : Surgery.Topology.Circle))
        (sigma.lift x) := rfl
  have hinward : (u.inwardConormal g z : E) = (diskMapInwardConormal g U (z : ℂ) : E) :=
    SmoothDisk.inwardConormal_eq_diskMapInwardConormal u g hU z
  have hspeed : u.boundarySpeed g x =
      2 * Real.pi * Real.sqrt (diskMapConformalCoefficient g U (z : ℂ)) := by
    rw [SmoothDisk.boundarySpeed_eq_diskMapConformalCoefficient u g hU x
      (by rw [← hz]; exact hconf (z : ℂ) hzmem), hz]
  rw [diskMapTraceBoundaryDensity, ← hz, hpoint, hcurve, hφ, hspeed, ← hinward]
  ring

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
