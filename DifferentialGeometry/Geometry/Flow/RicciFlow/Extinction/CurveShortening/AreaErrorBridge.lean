import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariationBoundaryFlux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [FiniteDimensional ℝ E] in
theorem inner_sub_smul_self (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (p : Q)
    (W T : TangentSpace 𝓘(ℝ, E) p) (a : ℝ) :
    g.inner p (W - a • T) (W - a • T) =
      g.inner p W W - 2 * a * g.inner p W T + a ^ 2 * g.inner p T T := by
  rw [map_sub (g.inner p), map_smul (g.inner p), sub_apply, smul_apply, smul_eq_mul]
  simp only [map_sub, map_smul, smul_eq_mul, g.symm p T W]
  ring

omit [FiniteDimensional ℝ E] in
theorem inner_smul_self_sq (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (p : Q)
    (T : TangentSpace 𝓘(ℝ, E) p) (a : ℝ) :
    g.inner p (a • T) (a • T) = a ^ 2 * g.inner p T T := by
  rw [map_smul (g.inner p), smul_apply, smul_eq_mul, map_smul (g.inner p T), smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
theorem inner_sub_smul_self_eq_orthogonalProjection_add
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (p : Q)
    (W T : TangentSpace 𝓘(ℝ, E) p) (hT : 0 < g.inner p T T) :
    g.inner p (W - g.inner p W T • T) (W - g.inner p W T • T) =
      g.inner p (W - (g.inner p W T / g.inner p T T) • T)
        (W - (g.inner p W T / g.inner p T T) • T) +
      (g.inner p W ((Real.sqrt (g.inner p T T))⁻¹ • T)) ^ 2 *
        (g.inner p T T - 1) ^ 2 := by
  have hsqrt : Real.sqrt (g.inner p T T) ^ 2 = g.inner p T T := Real.sq_sqrt hT.le
  have ht : g.inner p W ((Real.sqrt (g.inner p T T))⁻¹ • T) =
      (Real.sqrt (g.inner p T T))⁻¹ * (g.inner p W T) := by
    rw [map_smul, smul_eq_mul]
  rw [inner_sub_smul_self, inner_sub_smul_self, ht]
  field_simp
  ring_nf
  rw [hsqrt]
  ring

omit [FiniteDimensional ℝ E] in
theorem inner_sub_smul_self_orthogonalProjection_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (p : Q)
    (W T : TangentSpace 𝓘(ℝ, E) p) (hT : 0 < g.inner p T T) :
    g.inner p (W - (g.inner p W T / g.inner p T T) • T)
        (W - (g.inner p W T / g.inner p T T) • T) ≤
      g.inner p (W - g.inner p W T • T) (W - g.inner p W T • T) := by
  rw [inner_sub_smul_self_eq_orthogonalProjection_add g p W T hT]
  have h1 : 0 ≤ (g.inner p W ((Real.sqrt (g.inner p T T))⁻¹ • T)) ^ 2 *
      (g.inner p T T - 1) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

omit [FiniteDimensional ℝ E] in
theorem sqrt_inner_sub_smul_self_orthogonalProjection_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (p : Q)
    (W T : TangentSpace 𝓘(ℝ, E) p) (hT : 0 < g.inner p T T) :
    Real.sqrt (g.inner p (W - (g.inner p W T / g.inner p T T) • T)
        (W - (g.inner p W T / g.inner p T T) • T)) ≤
      Real.sqrt (g.inner p (W - g.inner p W T • T) (W - g.inner p W T • T)) :=
  Real.sqrt_le_sqrt (inner_sub_smul_self_orthogonalProjection_le g p W T hT)

omit [FiniteDimensional ℝ E] in
theorem orthogonalProjection_smul_eq_unitTangentProjection
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (p : Q)
    (W T : TangentSpace 𝓘(ℝ, E) p) (a : ℝ) (ha : a ≠ 0) :
    W - (g.inner p W (a • T) / g.inner p (a • T) (a • T)) • (a • T) =
      W - g.inner p W ((Real.sqrt (g.inner p T T))⁻¹ • T) •
        ((Real.sqrt (g.inner p T T))⁻¹ • T) := by
  have hq : 0 ≤ g.inner p T T := metric_inner_self_nonneg g p T
  have hsqrt : Real.sqrt (g.inner p T T) ^ 2 = g.inner p T T := Real.sq_sqrt hq
  have hsmul : g.inner p (a • T) (a • T) = a ^ 2 * g.inner p T T :=
    inner_smul_self_sq g p T a
  have hinner : g.inner p W (a • T) = a * g.inner p W T := by
    rw [map_smul, smul_eq_mul]
  have hinner2 : g.inner p W ((Real.sqrt (g.inner p T T))⁻¹ • T) =
      (Real.sqrt (g.inner p T T))⁻¹ * g.inner p W T := by
    rw [map_smul, smul_eq_mul]
  rw [hsmul, hinner, hinner2]
  congr 1
  simp only [smul_smul]
  congr 1
  by_cases hT0 : g.inner p T T = 0
  · simp [hT0]
  · have hpos : 0 < g.inner p T T := lt_of_le_of_ne hq (Ne.symm hT0)
    have hsq : Real.sqrt (g.inner p T T) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
    ring_nf
    rw [hsqrt]

omit [FiniteDimensional ℝ E] in
theorem orthogonalProjection_eq_unitTangentProjection
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (p : Q)
    (W T : TangentSpace 𝓘(ℝ, E) p) :
    W - (g.inner p W T / g.inner p T T) • T =
      W - g.inner p W ((Real.sqrt (g.inner p T T))⁻¹ • T) •
        ((Real.sqrt (g.inner p T T))⁻¹ • T) := by
  have h := orthogonalProjection_smul_eq_unitTangentProjection g p W T 1 one_ne_zero
  simpa only [one_smul] using h

def SmoothDisk.boundaryUnitTangent (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (x : ℝ) :
    TangentSpace 𝓘(ℝ, E) (u.map (diskBoundary (x : Surgery.Topology.Circle))) :=
  (u.boundarySpeed g x)⁻¹ • u.boundaryTangent (diskBoundary (x : Surgery.Topology.Circle))

def SmoothDisk.boundaryNormalVelocityProjection (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) (x : ℝ) :
    TangentSpace 𝓘(ℝ, E) (u.map (diskBoundary (x : Surgery.Topology.Circle))) :=
  let T := u.boundaryTangent (diskBoundary (x : Surgery.Topology.Circle))
  let W := u.boundaryNormalVelocity g gamma sigma htrace V x
  W - (g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle))) W T /
    g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle))) T T) • T

def SmoothDisk.boundaryNormalVelocityErrorDensity (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) (x : ℝ) : ℝ :=
  Real.sqrt (g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
      (u.boundaryNormalVelocityProjection g gamma sigma htrace V x)
      (u.boundaryNormalVelocityProjection g gamma sigma htrace V x)) * u.boundarySpeed g x

theorem SmoothDisk.boundaryNormalVelocityErrorDensity_eq_unitTangentProjection
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z)) (x : ℝ) :
    u.boundaryNormalVelocityErrorDensity g gamma sigma htrace V x =
      Real.sqrt (g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (u.boundaryNormalVelocity g gamma sigma htrace V x -
          g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
            (u.boundaryNormalVelocity g gamma sigma htrace V x) (u.boundaryUnitTangent g x) •
            u.boundaryUnitTangent g x)
        (u.boundaryNormalVelocity g gamma sigma htrace V x -
          g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
            (u.boundaryNormalVelocity g gamma sigma htrace V x) (u.boundaryUnitTangent g x) •
            u.boundaryUnitTangent g x)) * u.boundarySpeed g x := by
  simp only [SmoothDisk.boundaryNormalVelocityErrorDensity, SmoothDisk.boundaryUnitTangent,
    SmoothDisk.boundarySpeed, SmoothDisk.boundaryTangent,
    SmoothDisk.boundaryNormalVelocityProjection]
  rw [orthogonalProjection_eq_unitTangentProjection]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem SmoothDisk.curveOfLoopFamily_lift_eq_map_diskBoundary
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop Q) (t : ℝ)
    (hslice : ∀ θ : Surgery.Topology.Circle, γ t θ = gamma θ) (x : ℝ) :
    (curveOfLoopFamily γ).lift (sigma.lift x) t =
      u.map (diskBoundary (x : Surgery.Topology.Circle)) := by
  rw [CurveMap.lift, curveOfLoopFamily, htrace (x : Surgery.Topology.Circle), sigma.lift_eq x]
  exact hslice (sigma.lift x : Surgery.Topology.Circle)

theorem SmoothDisk.boundaryNormalVelocityErrorDensity_eq_curve
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z))
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop Q)
    (J : Set ℝ) (t : ℝ)
    (hpoint : ∀ x : ℝ, (curveOfLoopFamily γ).lift (sigma.lift x) t =
      u.map (diskBoundary (x : Surgery.Topology.Circle)))
    (hvelocity : ∀ x : ℝ, V (diskBoundary (x : Surgery.Topology.Circle)) =
      (curveOfLoopFamily γ).velocity (I := 𝓘(ℝ, E)) J (sigma.lift x) t)
    (hcurvature : ∀ x : ℝ, u.boundaryCurvatureVelocity (G t) gamma sigma htrace x =
      (curveOfLoopFamily γ).curvatureVector G (sigma.lift x) t)
    (htangent : ∀ x : ℝ, u.boundaryTangent (diskBoundary (x : Surgery.Topology.Circle)) =
      deriv (sigma.lift) x • (curveOfLoopFamily γ).X (I := 𝓘(ℝ, E)) (sigma.lift x) t)
    (x : ℝ) :
    u.boundaryNormalVelocityErrorDensity (G t) gamma sigma htrace V x =
      (Real.sqrt ((curveOfLoopFamily γ).normSq G ((curveOfLoopFamily γ).normalVelocityError G J)
          (sigma.lift x) t) * (curveOfLoopFamily γ).speed G (sigma.lift x) t) *
        deriv (sigma.lift) x := by
  set c : CurveMap Q := curveOfLoopFamily γ with hc
  set a : ℝ := deriv (sigma.lift) x with ha
  set z : Disk := diskBoundary (x : Surgery.Topology.Circle) with hz
  have hpointx : c.lift (sigma.lift x) t = u.map z := by rw [hpoint x, hz]
  have hW : u.boundaryNormalVelocity (G t) gamma sigma htrace V x =
      c.velocity J (sigma.lift x) t - c.curvatureVector G (sigma.lift x) t := by
    rw [SmoothDisk.boundaryNormalVelocity, hvelocity x, hcurvature x]
    rfl
  have hT : u.boundaryTangent z = a • c.X (I := 𝓘(ℝ, E)) (sigma.lift x) t := by
    rw [hz, ha, hc, htangent x]
  have ha_nonneg : 0 ≤ a := by rw [ha]; exact sigma.monotone_lift.deriv_nonneg
  have hsp : u.boundarySpeed (G t) x = a * c.speed G (sigma.lift x) t := by
    have h1 : u.boundarySpeed (G t) x = Real.sqrt ((G t).inner (u.map z)
        (u.boundaryTangent z) (u.boundaryTangent z)) := rfl
    have hs2 : (c.speed G (sigma.lift x) t) ^ 2 =
        (G t).inner (c.lift (sigma.lift x) t) (c.X (sigma.lift x) t) (c.X (sigma.lift x) t) :=
      Real.sq_sqrt
        (metric_inner_self_nonneg (G t) (c.lift (sigma.lift x) t) (c.X (sigma.lift x) t))
    rw [h1, ← hpointx, hT, inner_smul_self_sq, ← hs2, Real.sqrt_mul (sq_nonneg a),
      Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg ha_nonneg,
      abs_of_nonneg (c.speed_nonneg G (sigma.lift x) t)]
  by_cases ha0 : a = 0
  · have hz0 : u.boundarySpeed (G t) x = 0 := by rw [hsp, ha0, zero_mul]
    simp only [SmoothDisk.boundaryNormalVelocityErrorDensity]
    rw [hz0, mul_zero, ha0, mul_zero]
  · have hproj : u.boundaryNormalVelocityProjection (G t) gamma sigma htrace V x =
        c.normalVelocityError G J (sigma.lift x) t := by
      simp only [SmoothDisk.boundaryNormalVelocityProjection, CurveMap.normalVelocityError,
        CurveMap.unitTangent, CurveMap.speed]
      rw [← hpointx, hW, hT]
      exact orthogonalProjection_smul_eq_unitTangentProjection (G t) (c.lift (sigma.lift x) t)
        (c.velocity J (sigma.lift x) t - c.curvatureVector G (sigma.lift x) t)
        (c.X (sigma.lift x) t) a ha0
    have hsqrt : Real.sqrt ((G t).inner (u.map z)
          (u.boundaryNormalVelocityProjection (G t) gamma sigma htrace V x)
          (u.boundaryNormalVelocityProjection (G t) gamma sigma htrace V x)) =
        Real.sqrt ((G t).inner (c.lift (sigma.lift x) t)
          (c.normalVelocityError G J (sigma.lift x) t)
          (c.normalVelocityError G J (sigma.lift x) t)) := by
      rw [hproj, ← hpointx]
    simp only [SmoothDisk.boundaryNormalVelocityErrorDensity, CurveMap.normSq]
    rw [hsqrt, hsp, ha, hc]
    ring

theorem intervalIntegral_comp_lift_mul_deriv_eq (sigma : SmoothWeaklyMonotoneCircleMap)
    (F : ℝ → ℝ) (hF : Continuous F) (hper : Function.Periodic F 1) :
    (∫ x in (0 : ℝ)..1, F (sigma.lift x) * deriv (sigma.lift) x) =
      ∫ y in (0 : ℝ)..1, F y := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (sigma.lift) (deriv (sigma.lift) x) x :=
    fun x _ => (sigma.smooth_lift.differentiable (by simp) x).hasDerivAt
  have hcont : ContinuousOn (deriv (sigma.lift)) (uIcc (0 : ℝ) 1) :=
    (sigma.smooth_lift.continuous_deriv (by simp)).continuousOn
  have hmain := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := 1) hderiv hcont hF
  have hinc : sigma.lift 1 = sigma.lift 0 + 1 := by simpa using sigma.increment 0
  rw [hinc] at hmain
  simp only [Function.comp_apply] at hmain
  rw [hmain]
  simpa using hper.intervalIntegral_add_eq (sigma.lift 0) 0

theorem SmoothDisk.integral_boundaryNormalVelocityErrorDensity_eq_areaError
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q) (gamma : RegularLoop 𝓘(ℝ, E) Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z))
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop Q)
    (J : Set ℝ) (t : ℝ)
    (hpoint : ∀ x : ℝ, (curveOfLoopFamily γ).lift (sigma.lift x) t =
      u.map (diskBoundary (x : Surgery.Topology.Circle)))
    (hvelocity : ∀ x : ℝ, V (diskBoundary (x : Surgery.Topology.Circle)) =
      (curveOfLoopFamily γ).velocity (I := 𝓘(ℝ, E)) J (sigma.lift x) t)
    (hcurvature : ∀ x : ℝ, u.boundaryCurvatureVelocity (G t) gamma sigma htrace x =
      (curveOfLoopFamily γ).curvatureVector G (sigma.lift x) t)
    (htangent : ∀ x : ℝ, u.boundaryTangent (diskBoundary (x : Surgery.Topology.Circle)) =
      deriv (sigma.lift) x • (curveOfLoopFamily γ).X (I := 𝓘(ℝ, E)) (sigma.lift x) t)
    (hcontinuous : Continuous (fun y : ℝ => Real.sqrt ((curveOfLoopFamily γ).normSq G
        ((curveOfLoopFamily γ).normalVelocityError G J) y t) * (curveOfLoopFamily γ).speed G y t))
    (hperiodic : Function.Periodic (fun y : ℝ => Real.sqrt ((curveOfLoopFamily γ).normSq G
        ((curveOfLoopFamily γ).normalVelocityError G J) y t) *
        (curveOfLoopFamily γ).speed G y t) 1) :
    (∫ x in (0 : ℝ)..1, u.boundaryNormalVelocityErrorDensity (G t) gamma sigma htrace V x) =
      (curveOfLoopFamily γ).areaError G J t := by
  have hρ : ∀ x ∈ uIcc (0 : ℝ) 1,
      u.boundaryNormalVelocityErrorDensity (G t) gamma sigma htrace V x =
        (fun y : ℝ => Real.sqrt ((curveOfLoopFamily γ).normSq G
          ((curveOfLoopFamily γ).normalVelocityError G J) y t) *
          (curveOfLoopFamily γ).speed G y t) (sigma.lift x) * deriv (sigma.lift) x := by
    intro x _
    exact u.boundaryNormalVelocityErrorDensity_eq_curve G gamma sigma htrace V γ J t
      hpoint hvelocity hcurvature htangent x
  rw [intervalIntegral.integral_congr hρ,
    intervalIntegral_comp_lift_mul_deriv_eq sigma _ hcontinuous hperiodic]
  simp only [CurveMap.areaError, CurveMap.integral]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
