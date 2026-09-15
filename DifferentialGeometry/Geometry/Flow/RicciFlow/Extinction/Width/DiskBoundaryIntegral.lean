import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Periodicity
import DifferentialGeometry.Geometry.Curvature.DiskCurvatureInequality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariationBoundary

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem CurveMap.smoothOn_of_contMDiff_loop (γ : Surgery.Topology.Circle → Q)
    (h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : Surgery.Topology.Circle))) :
    CurveMap.SmoothOn (fun θ _ => γ θ : CurveMap Q) (I := 𝓘(ℝ, E)) univ := by
  rw [CurveMap.SmoothOn]
  intro p _
  have hfst : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (Prod.fst : ℝ × ℝ → ℝ)
      (univ ×ˢ univ) p := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_fst
  exact ((h p.1).contMDiffWithinAt).comp p hfst (fun q _ => mem_univ _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem CurveMap.immersedOn_of_loopVelocity_ne_zero (γ : Surgery.Topology.Circle → Q)
    (h : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun t : ℝ => γ (t : Surgery.Topology.Circle)) x 1 ≠ 0) :
    CurveMap.ImmersedOn (fun θ _ => γ θ : CurveMap Q) (I := 𝓘(ℝ, E)) univ :=
  fun x _ _ => h x

omit [CompleteSpace E] in
theorem CurveMap.riemannianCurveCurvature_loop_add_period
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : Surgery.Topology.Circle → Q)
    (hsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : Surgery.Topology.Circle)))
    (himm : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun t : ℝ => γ (t : Surgery.Topology.Circle)) x 1 ≠ 0) (y : ℝ) :
    riemannianCurveCurvature g (fun t : ℝ => γ (t : Surgery.Topology.Circle)) (y + 1) =
      riemannianCurveCurvature g (fun t : ℝ => γ (t : Surgery.Topology.Circle)) y := by
  have h := CurveMap.curvatureVector_add_period (I := 𝓘(ℝ, E)) (fun _ => g)
    (fun θ _ => γ θ) univ (CurveMap.smoothOn_of_contMDiff_loop γ hsm)
    (CurveMap.immersedOn_of_loopVelocity_ne_zero γ himm) 0 (mem_univ 0) y
  simpa only [CurveMap.lift,
    DifferentialGeometry.PDE.RicciFlow.Extinction.Width.CurveMap.curvatureVector_loop_eq_riemannianCurveCurvature]
    using h

omit [CompleteSpace E] in
theorem CurveMap.riemannianCurveCurvature_loop_periodic
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : Surgery.Topology.Circle → Q)
    (hsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : Surgery.Topology.Circle)))
    (himm : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun t : ℝ => γ (t : Surgery.Topology.Circle)) x 1 ≠ 0) :
    Function.Periodic (fun y : ℝ =>
      riemannianCurveCurvature g (fun t : ℝ => γ (t : Surgery.Topology.Circle)) y) 1 :=
  fun y => CurveMap.riemannianCurveCurvature_loop_add_period g γ hsm himm y

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

theorem SmoothDisk.integral_boundaryCurvatureDensity_eq_diskMapTraceBoundaryDensity
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (γ : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta))
    (hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U z)
    (hsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ.toContinuousLoop))
    (himm : ∀ x, loopVelocity (I := 𝓘(ℝ, E)) γ.toContinuousLoop x ≠ 0) :
    (∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g γ sigma htrace x) =
      ∫ θ in -Real.pi..Real.pi,
        diskMapTraceBoundaryDensity g U
          (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle))
          (fun θ => sigma.lift (θ / (2 * Real.pi))) θ := by
  set γR : ℝ → Q := fun t => γ (t : Surgery.Topology.Circle) with hγRdef
  set φ : ℝ → ℝ := fun θ => sigma.lift (θ / (2 * Real.pi)) with hφdef
  set D : ℝ → ℝ := fun θ =>
    g.inner (U (circleMap 0 1 θ))
      ((riemannianCurveCurvature g γR (φ θ) : E))
      ((diskMapInwardConormal g U (circleMap 0 1 θ) : E)) *
      Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ)) with hDdef
  have hφper : ∀ θ, φ (θ + 2 * Real.pi) = φ θ + 1 := by
    intro θ
    have hθ : (θ + 2 * Real.pi) / (2 * Real.pi) = θ / (2 * Real.pi) + 1 := by
      field_simp
    simp only [φ, hθ, sigma.increment]
  have hcurv : Function.Periodic (fun y : ℝ => riemannianCurveCurvature g γR y) 1 := by
    rw [hγRdef]
    exact CurveMap.riemannianCurveCurvature_loop_periodic g γ.toContinuousLoop hsm himm
  have hDper : Function.Periodic D (2 * Real.pi) := by
    intro θ
    have hz := periodic_circleMap 0 1 θ
    have hc : (riemannianCurveCurvature g γR (φ θ + 1) : E) =
        (riemannianCurveCurvature g γR (φ θ) : E) := congrArg (fun v => (v : E)) (hcurv (φ θ))
    dsimp only [D]
    rw [hz, hφper θ, hc]
  have hpoint : ∀ x : ℝ, u.boundaryCurvatureDensity g γ sigma htrace x =
      2 * Real.pi * D (2 * Real.pi * x) := by
    intro x
    rw [hDdef]
    rw [SmoothDisk.boundaryCurvatureDensity_eq_diskMapTraceBoundaryDensity
      u g hU γ sigma htrace hconf x]
    rw [← hγRdef]
    simp only [diskMapTraceBoundaryDensity]
    have harg : sigma.lift (2 * Real.pi * x / (2 * Real.pi)) = φ (2 * Real.pi * x) := by
      rw [hφdef]
    rw [harg]
  have hscale : (∫ x in (0 : ℝ)..1, 2 * Real.pi * D (2 * Real.pi * x)) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), D θ := by
    rw [intervalIntegral.integral_const_mul]
    have hsmul : (2 * Real.pi) • (∫ x in (0 : ℝ)..1, D (2 * Real.pi * x)) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), D θ := by
      simpa using intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : ℝ)) (b := (1 : ℝ)) (c := 2 * Real.pi) (f := D)
    simpa only [smul_eq_mul] using hsmul
  have hshift : (∫ θ in (0 : ℝ)..(2 * Real.pi), D θ) =
      ∫ θ in -Real.pi..Real.pi, D θ := by
    have h := hDper.intervalIntegral_add_eq (t := (0 : ℝ)) (s := -Real.pi)
    have hb : -Real.pi + 2 * Real.pi = Real.pi := by ring
    simpa [hb] using h
  have hDfun : D = fun θ => diskMapTraceBoundaryDensity g U γR φ θ := by
    rw [hDdef]
    funext θ
    simp only [diskMapTraceBoundaryDensity]
  have hDint : (∫ θ in -Real.pi..Real.pi,
        diskMapTraceBoundaryDensity g U γR φ θ) =
      ∫ θ in -Real.pi..Real.pi, D θ := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [hDfun]
  calc (∫ x in (0 : ℝ)..1,
        u.boundaryCurvatureDensity g γ sigma htrace x)
      = ∫ x in (0 : ℝ)..1, 2 * Real.pi * D (2 * Real.pi * x) :=
        intervalIntegral.integral_congr fun x _ => hpoint x
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), D θ := hscale
    _ = ∫ θ in -Real.pi..Real.pi, D θ := hshift
    _ = ∫ θ in -Real.pi..Real.pi,
        diskMapTraceBoundaryDensity g U γR φ θ := hDint.symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [CompactSpace Q]

theorem SmoothDisk.curvature_inequality_standardModel
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (hnonconstant : ¬ ∃ q : Q, ∀ z : Disk, u.map z = q)
    (hconformal : u.IsConformal g) (hharmonic : u.IsHarmonic g)
    (γ : RegularLoop 𝓘(ℝ, E) Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ.toContinuousLoop))
    (himm : ∀ x, loopVelocity (I := 𝓘(ℝ, E)) γ.toContinuousLoop x ≠ 0)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta)) :
    IntegrableOn (diskExtension (u.sectionalDensity g)) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryCurvatureDensity g γ sigma htrace) volume 0 1 ∧
      2 * Real.pi ≤
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.sectionalDensity g) z) +
        ∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g γ sigma htrace x := by
  obtain ⟨U, hU⟩ := SmoothDisk.exists_smoothDiskExtension u
  obtain ⟨N, hN, hDN, hUsm⟩ := hU.2
  have hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U z :=
    (SmoothDisk.isConformal_iff_diskMapConformalAt u g hU).mp hconformal
  have hharm : ∀ q ∈ Metric.ball (0 : ℂ) 1, (diskMapTension g U q : E) = 0 :=
    fun q hq => SmoothDisk.diskMapTension_eq_zero_of_isHarmonic u g hU ⟨q, Metric.ball_subset_closedBall hq⟩ hharmonic
  let φ : ℝ → ℝ := fun θ => sigma.lift (θ / (2 * Real.pi))
  have hφcd : ContDiff ℝ ∞ φ :=
    sigma.smooth_lift.comp (contDiff_id.div_const _)
  have hφmono : Monotone φ :=
    fun a b hab => sigma.monotone_lift (div_le_div_of_nonneg_right hab (by positivity))
  have hφlift : ∀ θ, (φ θ : Surgery.Topology.Circle) =
      sigma.map ((θ / (2 * Real.pi) : ℝ) : Surgery.Topology.Circle) :=
    fun θ => (sigma.lift_eq (θ / (2 * Real.pi))).symm
  have hγR : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t : ℝ => γ (t : Surgery.Topology.Circle)) := hγ
  have hiR : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun t : ℝ => γ (t : Surgery.Topology.Circle)) t 1 ≠ 0 := himm
  have htrace' : DifferentialGeometry.Topology.diskTrace u.map = γ.toContinuousLoop.comp sigma.map := by
    ext θ
    exact htrace θ
  have htraceφ : U ∘ circleMap 0 1 =
      (fun t : ℝ => γ (t : Surgery.Topology.Circle)) ∘ φ :=
    SmoothDiskExtension.angle_trace hU htrace' hφlift
  have hmain := SmoothDiskExtension.curvature_inequality g hU hconf hharm hnonconstant
    hγR hiR hφcd hφmono htraceφ
  have hBint : IntegrableOn (diskMapSectionalDensity g U) (Metric.closedBall (0 : ℂ) 1) :=
    integrableOn_diskMapSectionalDensity g hN hUsm (isCompact_closedBall 0 1) hDN hconf
  have hint1 : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapSectionalDensity g U z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.sectionalDensity g) z :=
    integral_congr_ae (SmoothDisk.sectionalDensity_ae_eq u g U hU)
  have hDcont : ContDiff ℝ ∞ (fun θ : ℝ =>
      diskMapTraceBoundaryDensity g U (fun t : ℝ => γ (t : Surgery.Topology.Circle)) φ θ) :=
    contDiff_diskMapTraceBoundaryDensity g hN hUsm hDN hconf hγR hiR hφcd htraceφ
  have hpt (x : ℝ) : u.boundaryCurvatureDensity g γ sigma htrace x =
      2 * Real.pi * diskMapTraceBoundaryDensity g U
        (fun t : ℝ => γ (t : Surgery.Topology.Circle)) φ (2 * Real.pi * x) := by
    rw [SmoothDisk.boundaryCurvatureDensity_eq_diskMapTraceBoundaryDensity
      u g hU γ sigma htrace hconf x]
  have hint2 := SmoothDisk.integral_boundaryCurvatureDensity_eq_diskMapTraceBoundaryDensity
    u g hU γ sigma htrace hconf hγ himm
  have hcont2 : Continuous (fun x : ℝ => 2 * Real.pi * diskMapTraceBoundaryDensity g U
      (fun t : ℝ => γ (t : Surgery.Topology.Circle)) φ (2 * Real.pi * x)) :=
    continuous_const.mul (hDcont.continuous.comp (continuous_const.mul continuous_id))
  refine ⟨hBint.congr_fun_ae (SmoothDisk.sectionalDensity_ae_eq u g U hU), ?_, ?_⟩
  · exact (hcont2.intervalIntegrable 0 1).congr (fun x _ => (hpt x).symm)
  · rw [← hint1, hint2]
    exact hmain

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
