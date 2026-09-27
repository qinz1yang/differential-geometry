import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariationBoundary
import DifferentialGeometry.Geometry.Metric.Conformal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem inner_sub_smul_eq_inner_of_inner_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (W T ν : TangentSpace 𝓘(ℝ, E) p) (a : ℝ) (hνT : g.inner p ν T = 0) :
    g.inner p (W - a • T) ν = g.inner p W ν := by
  rw [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, g.symm p T ν, hνT,
    mul_zero, sub_zero]

theorem inner_le_sqrt_inner_sub_smul_self_of_inner_eq_zero_and_inner_self_eq_one
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (W T ν : TangentSpace 𝓘(ℝ, E) p) (a : ℝ)
    (hνT : g.inner p ν T = 0) (hνν : g.inner p ν ν = 1) :
    g.inner p W ν ≤
      Real.sqrt (g.inner p (W - a • T) (W - a • T)) := by
  let D := (Tensor0SBundle.tangentMetricData (I := 𝓘(ℝ, E)) g p).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace 𝓘(ℝ, E) p) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) p) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace 𝓘(ℝ, E) p) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) p) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace 𝓘(ℝ, E) p) _ _ _ D.toCore.toCore
  have hg : ∀ v w : TangentSpace 𝓘(ℝ, E) p, g.inner p v w = Inner.inner ℝ v w := by
    intro v w
    rw [← Tensor0SBundle.TangentMetricData.inner_eq
      (Tensor0SBundle.tangentMetricData (I := 𝓘(ℝ, E)) g p) v w]
    change D.inner v w = Inner.inner ℝ v w
    exact (Tensor0SBundle.MetricFiberData.toCore_inner D v w).symm
  have hνnorm : ‖ν‖ = 1 := by
    have hsq : ‖ν‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, ← hg ν ν, hνν]
    nlinarith [norm_nonneg ν]
  have hsqrt : Real.sqrt (g.inner p (W - a • T) (W - a • T)) = ‖W - a • T‖ := by
    rw [hg (W - a • T) (W - a • T), real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg (W - a • T))]
  rw [hsqrt, ← inner_sub_smul_eq_inner_of_inner_eq_zero g p W T ν a hνT, hg _ ν]
  calc Inner.inner ℝ (W - a • T) ν ≤ ‖W - a • T‖ * ‖ν‖ := real_inner_le_norm _ _
    _ = ‖W - a • T‖ := by rw [hνnorm, mul_one]

theorem inner_le_sqrt_inner_sub_smul_self_attained :
    (euclideanMetric ℂ).inner (0 : ℂ) ((10 : ℂ) + Complex.I) (1 : ℂ) ≤
      Real.sqrt ((euclideanMetric ℂ).inner (0 : ℂ)
        (((10 : ℂ) + Complex.I) - (1 : ℝ) • Complex.I)
        (((10 : ℂ) + Complex.I) - (1 : ℝ) • Complex.I)) :=
  inner_le_sqrt_inner_sub_smul_self_of_inner_eq_zero_and_inner_self_eq_one
    (euclideanMetric ℂ) (0 : ℂ) ((10 : ℂ) + Complex.I) Complex.I (1 : ℂ) (1 : ℝ)
    (by simp) (by simp)

theorem not_inner_le_sqrt_inner_sub_smul_self_without_inner_eq_zero :
    ¬ (∀ (W T ν : ℂ) (a : ℝ),
      (euclideanMetric ℂ).inner (0 : ℂ) ν ν = 1 →
      (euclideanMetric ℂ).inner (0 : ℂ) W ν ≤
        Real.sqrt ((euclideanMetric ℂ).inner (0 : ℂ) (W - a • T) (W - a • T))) := by
  intro h
  have h1 := h ((10 : ℂ) + Complex.I) (1 : ℂ) (1 : ℂ) (10 : ℝ) (by simp)
  simp at h1

theorem not_inner_le_sqrt_inner_sub_smul_self_without_inner_self_eq_one :
    ¬ (∀ (W T ν : ℂ) (a : ℝ),
      (euclideanMetric ℂ).inner (0 : ℂ) ν T = 0 →
      (euclideanMetric ℂ).inner (0 : ℂ) W ν ≤
        Real.sqrt ((euclideanMetric ℂ).inner (0 : ℂ) (W - a • T) (W - a • T))) := by
  intro h
  have h1 := h Complex.I (1 : ℂ) (2 * Complex.I) (0 : ℝ) (by simp)
  simp at h1

theorem diskMapPartial_id_self (z v : ℂ) : diskMapPartial (E := ℂ) id z v = v := by
  rw [diskMapPartial, mfderiv_id]
  exact ContinuousLinearMap.id_apply v

theorem euclideanMetric_diskMapConformalCoefficient_id (z : ℂ) :
    diskMapConformalCoefficient (euclideanMetric ℂ) id z = 1 := by
  have h1 : diskMapPartial (E := ℂ) id z (1 : ℂ) = (1 : ℂ) := diskMapPartial_id_self z 1
  rw [diskMapConformalCoefficient, h1]
  change Inner.inner ℝ (1 : ℂ) (1 : ℂ) = 1
  simp

theorem euclideanMetric_diskMapConformalAt_id (z : ℂ) :
    DiskMapConformalAt (euclideanMetric ℂ) id z := by
  have h1 : diskMapPartial (E := ℂ) id z (1 : ℂ) = (1 : ℂ) := diskMapPartial_id_self z 1
  have hI : diskMapPartial (E := ℂ) id z Complex.I = Complex.I :=
    diskMapPartial_id_self z Complex.I
  constructor
  · rw [h1, hI]
    change Inner.inner ℝ (1 : ℂ) Complex.I = 0
    simp
  · rw [h1, hI]
    change Inner.inner ℝ (1 : ℂ) (1 : ℂ) = Inner.inner ℝ Complex.I Complex.I
    simp

theorem euclideanMetric_inwardConormal_id_unit {z : ℂ} (hz : ‖z‖ = 1) :
    (euclideanMetric ℂ).inner z (diskMapInwardConormal (euclideanMetric ℂ) id z)
      (diskMapInwardConormal (euclideanMetric ℂ) id z) = 1 :=
  (euclideanMetric_diskMapConformalAt_id z).inwardConormal_unit hz
    (by rw [euclideanMetric_diskMapConformalCoefficient_id]; norm_num)

theorem euclideanMetric_inwardConormal_id_orthogonal (z : ℂ) :
    (euclideanMetric ℂ).inner z (diskMapPartial id z (Complex.I * z))
      (diskMapInwardConormal (euclideanMetric ℂ) id z) = 0 :=
  (euclideanMetric_diskMapConformalAt_id z).inwardConormal_orthogonal

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold (𝓘(ℝ, E)) ∞ Q]

def SmoothDisk.boundaryTangent (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (z : Disk) :
    TangentSpace 𝓘(ℝ, E) (u.map z) :=
  u.differential z ((2 * Real.pi : ℝ) • (Complex.I * (z : ℂ)))

def SmoothDisk.boundaryCurvatureVelocity (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (x : ℝ) : TangentSpace 𝓘(ℝ, E) (u.map (diskBoundary (x : Surgery.Topology.Circle))) := by
  let z := diskBoundary (x : Surgery.Topology.Circle)
  let c : CurveMap Q := fun theta _ => gamma theta
  have V : TangentSpace 𝓘(ℝ, E) (u.map z) := by
    change TangentSpace 𝓘(ℝ, E) (u.map (diskBoundary (x : Surgery.Topology.Circle)))
    rw [htrace, sigma.lift_eq]
    exact c.curvatureVector (fun _ => g) (sigma.lift x) 0
  exact V

def SmoothDisk.boundaryNormalVelocity (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) (x : ℝ) :
    TangentSpace 𝓘(ℝ, E) (u.map (diskBoundary (x : Surgery.Topology.Circle))) :=
  V (diskBoundary (x : Surgery.Topology.Circle)) -
    u.boundaryCurvatureVelocity g gamma sigma htrace x

def SmoothDisk.boundaryNormalVelocityError (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) (x : ℝ) :
    TangentSpace 𝓘(ℝ, E) (u.map (diskBoundary (x : Surgery.Topology.Circle))) :=
  let T := u.boundaryTangent (diskBoundary (x : Surgery.Topology.Circle))
  let W := u.boundaryNormalVelocity g gamma sigma htrace V x
  W - (g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle))) W T /
    g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle))) T T) • T

def SmoothDisk.boundaryAreaError (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.sqrt
    (g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
      (u.boundaryNormalVelocityError g gamma sigma htrace V x)
      (u.boundaryNormalVelocityError g gamma sigma htrace V x)) * u.boundarySpeed g x

theorem SmoothDisk.boundaryCurvatureDensity_eq_inner_curvatureVelocity
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (x : ℝ) :
    u.boundaryCurvatureDensity g gamma sigma htrace x =
      g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (u.boundaryCurvatureVelocity g gamma sigma htrace x)
        (u.inwardConormal g (diskBoundary (x : Surgery.Topology.Circle))) *
        u.boundarySpeed g x := rfl

theorem SmoothDisk.boundaryFluxDensity_sub_boundaryCurvatureDensity
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) (x : ℝ) :
    u.boundaryFluxDensity g V x - u.boundaryCurvatureDensity g gamma sigma htrace x =
      g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (u.boundaryNormalVelocity g gamma sigma htrace V x)
        (u.inwardConormal g (diskBoundary (x : Surgery.Topology.Circle))) *
        u.boundarySpeed g x := by
  rw [SmoothDisk.boundaryFluxDensity,
    SmoothDisk.boundaryCurvatureDensity_eq_inner_curvatureVelocity,
    SmoothDisk.boundaryNormalVelocity]
  simp only [map_sub, sub_apply]
  ring

theorem SmoothDisk.boundaryFluxDensity_sub_boundaryCurvatureDensity_le
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) (x : ℝ)
    (hconf : DiskMapConformalAt g U (circleMap 0 1 (2 * Real.pi * x))) :
    u.boundaryFluxDensity g V x - u.boundaryCurvatureDensity g gamma sigma htrace x ≤
      Real.sqrt (g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (u.boundaryNormalVelocityError g gamma sigma htrace V x)
        (u.boundaryNormalVelocityError g gamma sigma htrace V x)) * u.boundarySpeed g x := by
  set z : Disk := diskBoundary (x : Surgery.Topology.Circle) with hzdef
  have hz : (z : ℂ) = circleMap 0 1 (2 * Real.pi * x) := by
    have h := diskBoundary_angle (2 * Real.pi * x)
    have hθ : 2 * Real.pi * x / (2 * Real.pi) = x := by field_simp
    rw [hθ] at h
    exact h
  have hconfz : DiskMapConformalAt g U (z : ℂ) := by rw [hz]; exact hconf
  have hpt : U (z : ℂ) = u.map z := hU.1 z
  have hco : (u.inwardConormal g z : E) = (diskMapInwardConormal g U (z : ℂ) : E) :=
    SmoothDisk.inwardConormal_eq_diskMapInwardConormal u g hU z
  rw [SmoothDisk.boundaryFluxDensity_sub_boundaryCurvatureDensity]
  simp only [SmoothDisk.boundaryNormalVelocityError]
  by_cases hpos : 0 < diskMapConformalCoefficient g U (z : ℂ)
  · have hz1 : ‖(z : ℂ)‖ = 1 := by rw [hz, circleMap]; simp [Complex.norm_exp]
    have hνν : g.inner (u.map z) (u.inwardConormal g z) (u.inwardConormal g z) = 1 := by
      have h := hconfz.inwardConormal_unit hz1 hpos
      rw [← hpt, hco]
      exact h
    have hνT : g.inner (u.map z) (u.inwardConormal g z) (u.boundaryTangent z) = 0 := by
      have hO := hconfz.inwardConormal_orthogonal
      have hT : u.boundaryTangent z =
          (2 * Real.pi : ℝ) • diskMapPartial (E := E) U (z : ℂ) (Complex.I * (z : ℂ)) := by
        rw [SmoothDisk.boundaryTangent, SmoothDisk.differential_eq_diskMapPartial u hU z,
          diskMapPartial]
        exact map_smul _ _ _
      rw [hT, ← hpt, hco,
        g.symm (U (z : ℂ)) (diskMapInwardConormal g U (z : ℂ))
          ((2 * Real.pi : ℝ) • diskMapPartial U (z : ℂ) (Complex.I * (z : ℂ))),
        map_smul, smul_apply, smul_eq_mul, hO, mul_zero]
    have hmain := inner_le_sqrt_inner_sub_smul_self_of_inner_eq_zero_and_inner_self_eq_one
      g (u.map z) (u.boundaryNormalVelocity g gamma sigma htrace V x) (u.boundaryTangent z)
      (u.inwardConormal g z)
      (g.inner (u.map z) (u.boundaryNormalVelocity g gamma sigma htrace V x)
        (u.boundaryTangent z) / g.inner (u.map z) (u.boundaryTangent z)
        (u.boundaryTangent z)) hνT hνν
    exact mul_le_mul_of_nonneg_right hmain (Real.sqrt_nonneg _)
  · have hz0 : diskMapConformalCoefficient g U (z : ℂ) = 0 :=
      le_antisymm (not_lt.mp hpos) (diskMapConformalCoefficient_nonneg g U (z : ℂ))
    have hsp : u.boundarySpeed g x = 0 := by
      rw [SmoothDisk.boundarySpeed_eq_diskMapConformalCoefficient u g hU x hconf, ← hz, hz0,
        Real.sqrt_zero, mul_zero]
    rw [hsp]
    simp

theorem SmoothDisk.boundaryFlux_sub_integral_boundaryCurvatureDensity_le_areaError
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (hconf : ∀ x ∈ Icc (0 : ℝ) 1, DiskMapConformalAt g U (circleMap 0 1 (2 * Real.pi * x)))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z))
    (hintFlux : IntervalIntegrable (u.boundaryFluxDensity g V) volume (0 : ℝ) 1)
    (hintCurv : IntervalIntegrable (u.boundaryCurvatureDensity g gamma sigma htrace)
      volume (0 : ℝ) 1)
    (hintError : IntervalIntegrable (fun x => Real.sqrt
      (g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (u.boundaryNormalVelocityError g gamma sigma htrace V x)
        (u.boundaryNormalVelocityError g gamma sigma htrace V x)) * u.boundarySpeed g x)
      volume (0 : ℝ) 1) :
    u.boundaryFlux g V -
      ∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g gamma sigma htrace x ≤
      u.boundaryAreaError g gamma sigma htrace V := by
  rw [SmoothDisk.boundaryFlux, SmoothDisk.boundaryAreaError,
    ← intervalIntegral.integral_sub hintFlux hintCurv]
  exact intervalIntegral.integral_mono_on (by norm_num) (hintFlux.sub hintCurv) hintError
    (fun x hx => SmoothDisk.boundaryFluxDensity_sub_boundaryCurvatureDensity_le
      u g gamma sigma htrace hU V x (hconf x hx))

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
