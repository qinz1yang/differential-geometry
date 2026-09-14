import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariationBoundaryFlux

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem neg_inner_le_sqrt_inner_sub_smul_self_of_inner_eq_zero_and_inner_self_eq_one
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (W T ν : TangentSpace 𝓘(ℝ, E) p) (a : ℝ)
    (hνT : g.inner p ν T = 0) (hνν : g.inner p ν ν = 1) :
    -(g.inner p W ν) ≤ Real.sqrt (g.inner p (W - a • T) (W - a • T)) := by
  have h := inner_le_sqrt_inner_sub_smul_self_of_inner_eq_zero_and_inner_self_eq_one
    g p (-W) T ν (-a) hνT hνν
  have harg : (-W) - (-a) • T = -(W - a • T) := by
    rw [neg_smul]
    abel
  simpa only [map_neg, neg_apply, harg, neg_neg] using h

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold (𝓘(ℝ, E)) ∞ Q]

theorem SmoothDisk.boundaryCurvatureDensity_sub_boundaryFluxDensity_le
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) (x : ℝ)
    (hconf : DiskMapConformalAt g U (circleMap 0 1 (2 * Real.pi * x))) :
    u.boundaryCurvatureDensity g gamma sigma htrace x - u.boundaryFluxDensity g V x ≤
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
  rw [← neg_sub (u.boundaryFluxDensity g V x)
    (u.boundaryCurvatureDensity g gamma sigma htrace x)]
  rw [SmoothDisk.boundaryFluxDensity_sub_boundaryCurvatureDensity]
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
    have hmain := neg_inner_le_sqrt_inner_sub_smul_self_of_inner_eq_zero_and_inner_self_eq_one
      g (u.map z) (u.boundaryNormalVelocity g gamma sigma htrace V x) (u.boundaryTangent z)
      (u.inwardConormal g z)
      (g.inner (u.map z) (u.boundaryNormalVelocity g gamma sigma htrace V x)
        (u.boundaryTangent z)) hνT hνν
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right hmain (Real.sqrt_nonneg _)
  · have hz0 : diskMapConformalCoefficient g U (z : ℂ) = 0 :=
      le_antisymm (not_lt.mp hpos) (diskMapConformalCoefficient_nonneg g U (z : ℂ))
    have hsp : u.boundarySpeed g x = 0 := by
      rw [SmoothDisk.boundarySpeed_eq_diskMapConformalCoefficient u g hU x hconf, ← hz, hz0,
        Real.sqrt_zero, mul_zero]
    rw [hsp]
    simp

theorem SmoothDisk.integral_boundaryCurvatureDensity_sub_boundaryFlux_le_areaError
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
    (∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g gamma sigma htrace x) -
        u.boundaryFlux g V ≤ u.boundaryAreaError g gamma sigma htrace V := by
  rw [SmoothDisk.boundaryFlux, ← intervalIntegral.integral_sub hintCurv hintFlux,
    SmoothDisk.boundaryAreaError]
  exact intervalIntegral.integral_mono_on (by norm_num) (hintCurv.sub hintFlux) hintError
    (fun x hx => SmoothDisk.boundaryCurvatureDensity_sub_boundaryFluxDensity_le
      u g gamma sigma htrace hU V x (hconf x hx))

theorem variation_le_of_curvatureFlux {B C D F Err S A Mv : ℝ}
    (hMv : Mv = -2 * B - C) (hcurv : 2 * Real.pi ≤ B + D)
    (hflux : -Err ≤ F - D) (hscal : S * A ≤ C) :
    (1 / 2 : ℝ) * Mv - F ≤ -2 * Real.pi - S * A / 2 + Err := by
  rw [hMv]
  linarith

theorem not_variation_le_of_curvatureFlux_of_reversed_flux :
    ¬ (∀ B C D F Err S A Mv : ℝ, Mv = -2 * B - C → 2 * Real.pi ≤ B + D →
      F - D ≤ Err → S * A ≤ C →
      (1 / 2 : ℝ) * Mv - F ≤ -2 * Real.pi - S * A / 2 + Err) := by
  intro h
  have hc := h (-1) 1 (2 * Real.pi + 1) 0 0 1 1 1 (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by norm_num)
  linarith [Real.pi_pos]


theorem SmoothDisk.transportedAreaVariation_le
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
      volume (0 : ℝ) 1)
    (C S Mv : ℝ)
    (hMv : Mv = -2 *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.sectionalDensity g) z) - C)
    (hcurv : 2 * Real.pi ≤
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.sectionalDensity g) z) +
        ∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g gamma sigma htrace x)
    (hscal : S * diskArea g u.map ≤ C) :
    (1 / 2 : ℝ) * Mv - u.boundaryFlux g V ≤
      -2 * Real.pi - S * diskArea g u.map / 2 +
        u.boundaryAreaError g gamma sigma htrace V := by
  have hflux := SmoothDisk.integral_boundaryCurvatureDensity_sub_boundaryFlux_le_areaError
    u g gamma sigma htrace hU hconf V hintFlux hintCurv hintError
  have hflux' : -u.boundaryAreaError g gamma sigma htrace V ≤
      u.boundaryFlux g V -
        ∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g gamma sigma htrace x := by
    linarith
  exact variation_le_of_curvatureFlux hMv hcurv hflux' hscal

theorem exists_variation_le_of_curvatureFlux_tight :
    ∃ B C D F Err S A Mv : ℝ, Mv = -2 * B - C ∧ 2 * Real.pi ≤ B + D ∧
      -Err ≤ F - D ∧ S * A ≤ C ∧
      (1 / 2 : ℝ) * Mv - F = -2 * Real.pi - S * A / 2 + Err :=
  ⟨0, 0, 2 * Real.pi, 2 * Real.pi, 0, 0, 1, 0, by norm_num, by linarith [Real.pi_pos],
    by linarith [Real.pi_pos], by norm_num, by ring⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
