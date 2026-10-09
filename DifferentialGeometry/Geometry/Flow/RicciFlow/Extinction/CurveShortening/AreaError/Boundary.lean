import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaErrorBridge
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskBoundaryMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Periodicity

section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem SmoothDisk.isotopyVelocity_boundary_eq_curve_velocity
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop Q)
    (sigma : SmoothWeaklyMonotoneCircleMap) {J : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ t₀ (sigma.map theta))
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) Q Q ∞)
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ J, ∀ theta, Phi t (γ t₀ theta) = γ t theta) (x : ℝ) :
    u.isotopyVelocity Phi J t₀ hid (diskBoundary (x : Surgery.Topology.Circle)) =
      (curveOfLoopFamily γ).velocity (I := 𝓘(ℝ, E)) J (sigma.lift x) t₀ := by
  change mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun t => Phi t (u.map (diskBoundary (x : Surgery.Topology.Circle)))) J t₀ 1 = _
  unfold CurveMap.velocity
  apply congrArg (fun L : ℝ →L[ℝ] E => L 1)
  apply mfderivWithin_congr_of_mem _ ht₀
  intro t ht
  rw [htrace, hboundary t ht, sigma.lift_eq]
  rfl


theorem SmoothDisk.boundaryCurvatureVelocity_eq_curve_curvatureVector [FiniteDimensional ℝ E]
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma (sigma.map theta))
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop Q) (t : ℝ)
    (hslice : γ t = gamma.toContinuousLoop) (x : ℝ) :
    u.boundaryCurvatureVelocity (G t) gamma sigma htrace x =
      (curveOfLoopFamily γ).curvatureVector G (sigma.lift x) t := by
  change riemannianCurveCurvature (G t) (fun y => gamma (y : Surgery.Topology.Circle))
      (sigma.lift x) = riemannianCurveCurvature (G t)
        (fun y : ℝ => γ t (y : Surgery.Topology.Circle)) (sigma.lift x)
  have hs : (fun y : ℝ => γ t (y : Surgery.Topology.Circle)) =
      fun y : ℝ => gamma (y : Surgery.Topology.Circle) := by
    rw [hslice]
  rw [hs]

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem SmoothDisk.boundaryTangent_eq_deriv_lift_smul_loopVelocity
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma (sigma.map theta))
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U) (x : ℝ) :
    u.boundaryTangent (diskBoundary (x : Surgery.Topology.Circle)) =
      deriv sigma.lift x • loopVelocity (I := 𝓘(ℝ, E)) gamma.toContinuousLoop (sigma.lift x) := by
  obtain ⟨hUeq, N, hN, hDN, hUN⟩ := hU
  have hangle (y : ℝ) :
      (diskBoundary (y : Surgery.Topology.Circle) : ℂ) = circleMap 0 1 (2 * Real.pi * y) := by
    have h := diskBoundary_angle (2 * Real.pi * y)
    rwa [mul_div_cancel_left₀ y (by positivity : (2 * Real.pi) ≠ 0)] at h
  have hUat : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U
      (circleMap 0 1 (2 * Real.pi * x)) :=
    (hUN.contMDiffAt (hN.mem_nhds (hDN (circleMap_mem_closedBall 0 (by norm_num)
      _)))).mdifferentiableAt
      (by simp)
  have hboundary : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ circleMap 0 1)
      (2 * Real.pi * x) :=
    hUat.comp _ (differentiable_circleMap 0 1 _).mdifferentiableAt
  have hscale : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
  have hchain := congrArg (fun p : TangentBundle 𝓘(ℝ, E) Q => (p.2 : E))
    (tangent_velocity_comp hboundary hscale.differentiableAt)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      ((U ∘ circleMap 0 1) ∘ (fun y : ℝ => 2 * Real.pi * y)) x 1 =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ circleMap 0 1) (2 * Real.pi * x)
      (deriv (fun y : ℝ => 2 * Real.pi * y) x) at hchain
  rw [hscale.deriv] at hchain
  have hfactor : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ circleMap 0 1) (2 * Real.pi * x)
      (2 * Real.pi) = (2 * Real.pi) •
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ circleMap 0 1) (2 * Real.pi * x) 1 := by
    rw [← map_smul]
    simp only [smul_eq_mul, mul_one]
  rw [hfactor, mfderiv_diskMapBoundary hUat] at hchain
  have hleft : u.boundaryTangent (diskBoundary (x : Surgery.Topology.Circle)) =
      (2 * Real.pi) • diskMapPartial U (circleMap 0 1 (2 * Real.pi * x))
        (Complex.I * circleMap 0 1 (2 * Real.pi * x)) := by
    rw [SmoothDisk.boundaryTangent,
      SmoothDisk.differential_eq_diskMapPartial u ⟨hUeq, N, hN, hDN, hUN⟩]
    rw [diskMapPartial, map_smul, hangle]
    rfl
  have hfun : ((U ∘ circleMap 0 1) ∘ (fun y : ℝ => 2 * Real.pi * y)) =
      loopLift gamma.toContinuousLoop ∘ sigma.lift := by
    funext y
    change U (circleMap 0 1 (2 * Real.pi * y)) = gamma (sigma.lift y : Surgery.Topology.Circle)
    rw [← hangle y, hUeq, htrace, sigma.lift_eq]
  rw [hfun] at hchain
  have hgamma := gamma.contMDiff_lift.mdifferentiable (by norm_num) (sigma.lift x)
  have hsigma := sigma.smooth_lift.differentiable (by simp) x
  have htracechain := congrArg (fun p : TangentBundle 𝓘(ℝ, E) Q => (p.2 : E))
    (tangent_velocity_comp hgamma hsigma)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (loopLift gamma.toContinuousLoop ∘ sigma.lift) x 1 =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (loopLift gamma.toContinuousLoop) (sigma.lift x)
      (deriv sigma.lift x) at htracechain
  rw [hleft, ← hchain, htracechain, loopVelocity, ← map_smul]
  simp only [smul_eq_mul, mul_one]


theorem SmoothDisk.boundaryAreaError_isotopy_eq_curve_areaError [FiniteDimensional ℝ E]
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma (sigma.map theta))
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop Q) {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hslice : γ t = gamma.toContinuousLoop)
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) Q Q ∞)
    (hid : ∀ q, Phi t q = q)
    (hboundary : ∀ s ∈ J, ∀ theta, Phi s (γ t theta) = γ s theta)
    (hcontinuous : Continuous (fun y : ℝ => Real.sqrt ((curveOfLoopFamily γ).normSq G
        ((curveOfLoopFamily γ).normalVelocityError G J) y t) * (curveOfLoopFamily γ).speed G y t))
    (hperiodic : Function.Periodic (fun y : ℝ => Real.sqrt ((curveOfLoopFamily γ).normSq G
        ((curveOfLoopFamily γ).normalVelocityError G J) y t) *
        (curveOfLoopFamily γ).speed G y t) 1) :
    u.boundaryAreaError (G t) gamma sigma htrace (u.isotopyVelocity Phi J t hid) =
      (curveOfLoopFamily γ).areaError G J t := by
  have htraceγ : ∀ theta, u.map (diskBoundary theta) = γ t (sigma.map theta) := by
    rw [hslice]
    exact htrace
  apply SmoothDisk.integral_boundaryNormalVelocityErrorDensity_eq_areaError u G gamma sigma htrace
    (u.isotopyVelocity Phi J t hid) γ J t
  · exact SmoothDisk.curveOfLoopFamily_lift_eq_map_diskBoundary u gamma sigma htrace γ t
      (fun theta => congrArg (fun f : Surgery.Topology.ContinuousFreeLoop Q => f theta) hslice)
  · exact SmoothDisk.isotopyVelocity_boundary_eq_curve_velocity u γ sigma ht htraceγ Phi hid
      hboundary
  · exact SmoothDisk.boundaryCurvatureVelocity_eq_curve_curvatureVector u G gamma sigma htrace γ t
      hslice
  · intro x
    have htan := SmoothDisk.boundaryTangent_eq_deriv_lift_smul_loopVelocity u gamma sigma htrace hU
      x
    have hX : (curveOfLoopFamily γ).X (I := 𝓘(ℝ, E)) (sigma.lift x) t =
        loopVelocity (I := 𝓘(ℝ, E)) gamma.toContinuousLoop (sigma.lift x) := by
      change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun y : ℝ => γ t (y : Surgery.Topology.Circle))
          (sigma.lift x) 1 = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
            (fun y : ℝ => gamma.toContinuousLoop (y : Surgery.Topology.Circle)) (sigma.lift x) 1
      rw [hslice]
    rw [hX]
    exact htan
  · exact hcontinuous
  · exact hperiodic



end DifferentialGeometry.PDE.RicciFlow.Extinction.Width


namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuousOn_normalVelocityError_density [T2Space M] [I.Boundaryless] {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJreg : J ⊆ D.regular)
    (hJuniq : UniqueDiffOn ℝ J) (c : CurveMap M) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq g (c.normalVelocityError g J) p.1 p.2) * c.speed g p.1 p.2)
      (univ ×ˢ J) := by
  have hκ : Field.SmoothOn (I := I) (c.curvatureVector g) J :=
    Field.smoothOn_curvatureVector g hG hJreg hJuniq c hc hi
  have hv : CurveMap.Field.SmoothOn (I := I) (c.velocity (I := I) J) J :=
    CurveMap.Field.smoothOn_velocity c hc hJuniq
  have hW : CurveMap.Field.SmoothOn (I := I)
      (fun x t => c.velocity (I := I) J x t - c.curvatureVector g x t) J :=
    CurveMap.Field.smoothOn_sub hc _ _ hv hκ
  have hT : CurveMap.Field.SmoothOn (I := I) (c.unitTangent g) J :=
    CurveMap.Field.smoothOn_unitTangent g hG hJreg c hc hi
  have hinner : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (g p.2).inner (c.lift p.1 p.2)
      (c.velocity (I := I) J p.1 p.2 - c.curvatureVector g p.1 p.2)
      (c.unitTangent g p.1 p.2)) (univ ×ˢ J) :=
    CurveMap.Field.smoothOn_inner g hG hJreg c hc _ _ hW hT
  have hsmul : CurveMap.Field.SmoothOn (I := I)
      (fun x t => ((g t).inner (c.lift x t)
        (c.velocity (I := I) J x t - c.curvatureVector g x t)
        (c.unitTangent g x t)) • c.unitTangent g x t) J :=
    CurveMap.Field.smoothOn_const_smul c hc
      (fun x t => (g t).inner (c.lift x t)
        (c.velocity (I := I) J x t - c.curvatureVector g x t)
        (c.unitTangent g x t)) hinner (c.unitTangent g) hT
  have hNVE : CurveMap.Field.SmoothOn (I := I) (c.normalVelocityError g J) J :=
    (CurveMap.Field.smoothOn_sub hc _ _ hW hsmul).congr fun p hp => by
      simp only [CurveMap.normalVelocityError]
  have hnorm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      c.normSq g (c.normalVelocityError g J) p.1 p.2) (univ ×ˢ J) :=
    CurveMap.Field.smoothOn_inner g hG hJreg c hc (c.normalVelocityError g J)
      (c.normalVelocityError g J) hNVE hNVE
  have hsqrt : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq g (c.normalVelocityError g J) p.1 p.2)) (univ ×ˢ J) :=
    hnorm.continuousOn.sqrt
  have hspeed : ContinuousOn (fun p : ℝ × ℝ => c.speed g p.1 p.2) (univ ×ˢ J) :=
    (CurveMap.Field.smoothOn_speed g hG hJreg c hc hi).continuousOn
  have hint : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq g (c.normalVelocityError g J) p.1 p.2) * c.speed g p.1 p.2)
      (univ ×ˢ J) := hsqrt.mul hspeed
  exact hint

theorem periodic_normalVelocityError_density (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) {t : ℝ} (ht : t ∈ J) :
    Function.Periodic (fun x : ℝ => Real.sqrt (c.normSq g (c.normalVelocityError g J) x t) *
      c.speed g x t) 1 := by
  intro x
  have hγ := (c.smooth_slice hc ht).mdifferentiableAt (x := x + 1) (by simp)
  have hN : c.normalVelocityError g J (x + 1) t = c.normalVelocityError g J x t := by
    simp only [normalVelocityError, c.velocity_add_period J t x,
      c.curvatureVector_add_period g J hc hi t ht x, c.unitTangent_add_period g t x hγ]
    congr 5
    exact c.lift_add_period t x
  simp only [normSq, hN, c.speed_add_period g t x hγ]
  congr 5
  exact c.lift_add_period t x

theorem areaError_eq_of_subset
    (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J K : Set ℝ} (hc : c.SmoothOn (I := I) J) (hsub : K ⊆ J)
    {t : ℝ} (ht : t ∈ K) (hK : UniqueDiffWithinAt ℝ K t) :
    c.areaError g K t = c.areaError g J t := by
  have hvel (x : ℝ) : c.velocity (I := I) K x t =
      c.velocity (I := I) J x t := by
    have hdiff := (c.time_slice_contMDiffOn J hc x t (hsub ht)).mdifferentiableWithinAt (by simp)
    exact congrArg (fun L : ℝ →L[ℝ] E => L 1)
      (hdiff.mfderivWithin_mono hK.uniqueMDiffWithinAt hsub)
  have hnormal : ∀ x, c.normalVelocityError g K x t = c.normalVelocityError g J x t := by
    intro x
    simp only [CurveMap.normalVelocityError, hvel x]
  simp only [CurveMap.areaError, CurveMap.integral, CurveMap.normSq, hnormal]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap


namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q] [T2Space Q]

theorem SmoothDisk.boundaryAreaError_isotopy_eq_areaError [CompactSpace Q]
    {D : RealTimeInterval} (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hG : MetricFamilySmoothOn D G) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (hJuniq : UniqueDiffOn ℝ J)
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop Q)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := 𝓘(ℝ, E)) J)
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) J)
    {t : ℝ} (ht : t ∈ J)
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (hslice : γ t = gamma.toContinuousLoop)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma (sigma.map theta))
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) Q Q ∞)
    (hid : ∀ q, Phi t q = q)
    (hboundary : ∀ s ∈ J, ∀ theta, Phi s (γ t theta) = γ s theta) :
    u.boundaryAreaError (G t) gamma sigma htrace (u.isotopyVelocity Phi J t hid) =
      (curveOfLoopFamily γ).areaError G J t := by
  obtain ⟨U, hU⟩ := SmoothDisk.exists_smoothDiskExtension u
  have hcont : Continuous (fun y : ℝ => Real.sqrt ((curveOfLoopFamily γ).normSq G
      ((curveOfLoopFamily γ).normalVelocityError G J) y t) * (curveOfLoopFamily γ).speed G y t) :=
        by
    have hdensity := CurveMap.continuousOn_normalVelocityError_density G hG hJ hJuniq
      (curveOfLoopFamily γ) hγ hi
    have hcont' := hdensity.comp (continuous_id.prodMk continuous_const).continuousOn
      (show MapsTo (fun y : ℝ => (y, t)) univ (univ ×ˢ J) from fun y _ => ⟨mem_univ y, ht⟩)
    exact continuousOn_univ.mp hcont'
  exact SmoothDisk.boundaryAreaError_isotopy_eq_curve_areaError u G gamma sigma htrace hU
    γ ht hslice Phi hid hboundary hcont
    (CurveMap.periodic_normalVelocityError_density G (curveOfLoopFamily γ) hγ hi ht)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

end
