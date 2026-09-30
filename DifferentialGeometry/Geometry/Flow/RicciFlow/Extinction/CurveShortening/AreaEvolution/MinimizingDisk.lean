import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaError.Boundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ConformalAreaDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonEndpoint
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExistenceReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaError.Congruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Diffeomorphism
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaError.Diffeomorphism

section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [CompactSpace Q]

theorem SmoothDisk.integrableOn_scalar_mul_conformalFactor
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) :
    IntegrableOn (diskExtension (fun z : Disk =>
      metricScalarAt (I := 𝓘(ℝ, E)) g (u.map z) * u.conformalFactor g z))
      (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨U, hU⟩ := SmoothDisk.exists_smoothDiskExtension u
  obtain ⟨hUeq, N, hN, hDN, hUN⟩ := hU
  have hcont : ContinuousOn (fun z : ℂ => metricScalarAt (I := 𝓘(ℝ, E)) g (U z) *
      diskMapConformalCoefficient g U z) (Metric.closedBall (0 : ℂ) 1) :=
    ((metricScalar_smooth g).continuous.comp_continuousOn (hUN.continuousOn.mono hDN)).mul
      ((contDiffOn_diskMapConformalCoefficient g hN hUN).continuousOn.mono hDN)
  refine (hcont.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
  rw [show diskExtension (fun w : Disk => metricScalarAt (I := 𝓘(ℝ, E)) g (u.map w) *
      u.conformalFactor g w) z = metricScalarAt (I := 𝓘(ℝ, E)) g (u.map ⟨z, hz⟩) *
      u.conformalFactor g ⟨z, hz⟩ from dite_eq_left hz]
  rw [SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient u g ⟨hUeq, N, hN, hDN, hUN⟩,
    hUeq ⟨z, hz⟩]


omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] [T2Space Q] [CompactSpace Q] in
theorem SmoothDisk.nonconstant_of_embedded_trace
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma (sigma.map theta))
    (hemb : Topology.IsEmbedding (gamma : Surgery.Topology.Circle → Q)) :
    ¬ ∃ q : Q, ∀ z : Disk, u.map z = q := by
  have hσ : DifferentialGeometry.Geometry.IsWeaklyMonotoneOnce sigma.map :=
    ⟨sigma.lift, sigma.smooth_lift.continuous,
      fun t => (sigma.lift_eq t).symm, Or.inl ⟨sigma.monotone_lift, sigma.increment⟩⟩
  rintro ⟨q, hq⟩
  have hconst (theta : Surgery.Topology.Circle) : gamma theta = q := by
    obtain ⟨x, hx⟩ := hσ.surjective theta
    rw [← hx, ← htrace x]
    exact hq _
  have heq : (((1 / 2 : ℝ) : Surgery.Topology.Circle)) = 0 :=
    hemb.injective ((hconst _).trans (hconst _).symm)
  have hreal := (AddCircle.coe_eq_zero_iff_of_mem_Ico
    (p := (1 : ℝ)) (a := (1 / 2 : ℝ)) (by norm_num)).mp heq
  norm_num at hreal

theorem SmoothDisk.intervalIntegrable_boundaryNormalVelocityError_isotopy
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
    IntervalIntegrable (u.boundaryNormalVelocityErrorDensity (G t) gamma sigma htrace
      (u.isotopyVelocity Phi J t hid)) volume (0 : ℝ) 1 := by
  obtain ⟨U, hU⟩ := SmoothDisk.exists_smoothDiskExtension u
  have htraceγ : ∀ theta, u.map (diskBoundary theta) = γ t (sigma.map theta) := by
    rw [hslice]
    exact htrace
  have hpoint := SmoothDisk.curveOfLoopFamily_lift_eq_map_diskBoundary u gamma sigma htrace γ t
    (fun theta => congrArg (fun f : Surgery.Topology.ContinuousFreeLoop Q => f theta) hslice)
  have hvelocity := SmoothDisk.isotopyVelocity_boundary_eq_curve_velocity u γ sigma ht
    htraceγ Phi hid hboundary
  have hcurvature := SmoothDisk.boundaryCurvatureVelocity_eq_curve_curvatureVector
    u G gamma sigma htrace γ t hslice
  have htangent (x : ℝ) : u.boundaryTangent (diskBoundary (x : Surgery.Topology.Circle)) =
      deriv sigma.lift x • (curveOfLoopFamily γ).X (I := 𝓘(ℝ, E)) (sigma.lift x) t := by
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
  have hcont : Continuous (fun y : ℝ => Real.sqrt ((curveOfLoopFamily γ).normSq G
      ((curveOfLoopFamily γ).normalVelocityError G J) y t) * (curveOfLoopFamily γ).speed G y t) :=
        by
    have hdensity := CurveMap.continuousOn_normalVelocityError_density G hG hJ hJuniq
      (curveOfLoopFamily γ) hγ hi
    exact continuousOn_univ.mp (hdensity.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (show MapsTo (fun y : ℝ => (y, t)) univ (univ ×ˢ J) from fun y _ => ⟨mem_univ y, ht⟩))
  have heq : (u.boundaryNormalVelocityErrorDensity (G t) gamma sigma htrace
      (u.isotopyVelocity Phi J t hid)) = fun x : ℝ =>
      (Real.sqrt ((curveOfLoopFamily γ).normSq G ((curveOfLoopFamily γ).normalVelocityError G J)
        (sigma.lift x) t) * (curveOfLoopFamily γ).speed G (sigma.lift x) t) * deriv sigma.lift x :=
          by
    funext x
    exact SmoothDisk.boundaryNormalVelocityErrorDensity_eq_curve u G gamma sigma htrace
      (u.isotopyVelocity Phi J t hid) γ J t hpoint hvelocity hcurvature htangent x
  rw [heq]
  exact ((hcont.comp sigma.smooth_lift.continuous).mul
    (sigma.smooth_lift.continuous_deriv (by simp))).intervalIntegrable 0 1


variable [SigmaCompactSpace Q]

private theorem leastArea_slope_le_of_minimizingDisk_and_boundaryIsotopy
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := 𝓘(ℝ, E)) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (gamma : ℝ → RegularLoop 𝓘(ℝ, E) Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := 𝓘(ℝ, E)) (Icc a b))
    (hi : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).ImmersedOn
      (I := 𝓘(ℝ, E)) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (t : ℝ) (ht : t ∈ Ico a b)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t).toContinuousLoop)
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma t (sigma.map theta))
    (hconformal : u.IsConformal (B.family.metric t)) (hharmonic : u.IsHarmonic (B.family.metric t))
    (hmin : ∀ v : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = gamma t theta) →
        diskArea (B.family.metric t) u.map ≤ diskArea (B.family.metric t) v.map)
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) Q Q ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : Q × ℝ => Phi p.2 p.1) (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t q = q)
    (hboundary : ∀ s ∈ Icc a b, ∀ theta, Phi s (gamma t theta) = gamma s theta) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) (t + h) -
        loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) t) / h ≤
      -2 * Real.pi - scalarMinimum B.family t *
        loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) t / 2 +
      (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).areaError
        B.family.metric (Icc a b) t + ε := by
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have himm : ∀ s ∈ Icc a b, ∀ x,
      loopVelocity (I := 𝓘(ℝ, E)) (gamma s).toContinuousLoop x ≠ 0 :=
    fun s hs x => hi x s hs
  obtain ⟨_, hflux, _, hcontact, _, hslope⟩ := rfs_plateau_upper_comparison
    B.toSmoothMetricWindow t ht gamma hgamma hemb himm hctr u sigma htrace
    hconformal hharmonic hmin Phi hPhi hid hboundary
  have harea : diskArea (B.family.metric t) u.map =
      loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) t := by
    rw [SmoothDisk.transportedArea] at hcontact
    have heq : (fun z : Disk => Phi t (u.map z)) = u.map := funext fun z => hid (u.map z)
    rw [heq] at hcontact
    exact hcontact.symm
  have hmetric : ∀ z : Disk, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (B.family.metric r).inner (u.map z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (B.family.metric t) (u.map z) X Y) t := by
    intro z X Y
    have h := metricDerivAt (I := 𝓘(ℝ, E)) (M := Q)
      (show SolutionOn (I := 𝓘(ℝ, E)) (M := Q) D from ⟨B.family⟩)
      B.equation ⟨t, B.regular htcc⟩ (u.map z) X Y
    change HasDerivAt (fun r : ℝ => (B.family.metric r).inner (u.map z) X Y)
      (-2 * metricRicciAt (I := 𝓘(ℝ, E)) (B.family.metric t) (u.map z) (vec2 X Y)) t at h
    exact h.congr_deriv (congrArg (fun r : ℝ => -2 * r)
      (DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := 𝓘(ℝ, E))
        (B.family.metric t) (u.map z) X Y))
  have hbdd : BddBelow (Set.range (B.family.scalar t)) := by
    exact (isCompact_range (metricScalar_smooth (B.family.metric t)).continuous).bddBelow
  have hslice : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift (gamma t).toContinuousLoop) :=
    (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).smooth_slice hgamma htcc
  have herr := SmoothDisk.intervalIntegrable_boundaryNormalVelocityError_isotopy B.family.metric
    B.smooth B.regular (uniqueDiffOn_Icc B.lt) (fun s => (gamma s).toContinuousLoop)
    hgamma hi htcc u (gamma t) rfl sigma htrace Phi hid hboundary
  have hvar :=
    SmoothDisk.transportedAreaVariation_le_of_isConformal_isHarmonic_of_uniqueDiffWithinAt
    hdim B.family u ((uniqueDiffOn_Icc B.lt) t htcc) (gamma t) sigma htrace
    (u.nonconstant_of_embedded_trace (gamma t) sigma htrace (hemb t htcc))
    hconformal hharmonic hslice (himm t htcc) hmetric (u.isotopyVelocity Phi (Icc a b) t hid)
    hflux herr (u.integrableOn_scalar_mul_conformalFactor (B.family.metric t)) hbdd
  have herrEq := SmoothDisk.boundaryAreaError_isotopy_eq_areaError B.family.metric
    B.smooth B.regular (uniqueDiffOn_Icc B.lt) (fun s => (gamma s).toContinuousLoop)
    hgamma hi htcc u (gamma t) rfl sigma htrace Phi hid hboundary
  rw [harea, herrEq] at hvar
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hslope ε hε
  refine ⟨δ, hδ, fun h hh hb => ?_⟩
  linarith [hbound h hh hb]



private theorem leastArea_slope_le_of_minimizingDisk
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := 𝓘(ℝ, E)) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (gamma : ℝ → RegularLoop 𝓘(ℝ, E) Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := 𝓘(ℝ, E)) (Icc a b))
    (hi : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).ImmersedOn
      (I := 𝓘(ℝ, E)) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (t : ℝ) (ht : t ∈ Ico a b)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t).toContinuousLoop)
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma t (sigma.map theta))
    (hconformal : u.IsConformal (B.family.metric t)) (hharmonic : u.IsHarmonic (B.family.metric t))
    (hmin : ∀ v : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = gamma t theta) →
        diskArea (B.family.metric t) u.map ≤ diskArea (B.family.metric t) v.map) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) (t + h) -
        loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) t) / h ≤
      -2 * Real.pi - scalarMinimum B.family t *
        loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) t / 2 +
      (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).areaError
        B.family.metric (Icc a b) t + ε := by
  let : Nonempty Q := ⟨u.map diskCenter⟩
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  obtain ⟨r, hr, Phi, hPhi, hid, hboundary⟩ := rfs_csf_boundary_isotopy
    (fun s => (gamma s).toContinuousLoop) hgamma hi hemb t htcc B.lt
  let b' : ℝ := min b (t + r / 2)
  have htb' : t < b' := lt_min ht.2 (by linarith)
  have hb'b : b' ≤ b := min_le_left _ _
  have hsub : Icc t b' ⊆ Icc a b := Icc_subset_Icc ht.1 hb'b
  have hstrip : Icc t b' ⊆ Icc a b ∩ Ioo (t - r) (t + r) := by
    intro s hs
    refine ⟨hsub hs, ?_, ?_⟩
    · linarith [hs.1]
    · have hs' : s ≤ t + r / 2 := hs.2.trans (min_le_right _ _)
      linarith
  let B' : RicciBackground (I := 𝓘(ℝ, E)) (M := Q) D t b' :=
    { family := B.family, smooth := B.smooth, lt := htb', regular := fun s hs => B.regular (hsub
      hs),
      equation := B.equation, B₀ := B.B₀, B₁ := B.B₁, B₂ := B.B₂,
      B₀_nonneg := B.B₀_nonneg, B₁_nonneg := B.B₁_nonneg, B₂_nonneg := B.B₂_nonneg,
      ricci_bound := fun s hs p => B.ricci_bound s (hsub hs) p,
      riemann_bound := fun s hs p => B.riemann_bound s (hsub hs) p,
      nablaRicci_bound := fun s hs p => B.nablaRicci_bound s (hsub hs) p }
  have hgamma' : (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).SmoothOn
      (I := 𝓘(ℝ, E)) (Icc t b') :=
    hgamma.mono (Set.prod_mono (subset_univ _) hsub)
  have hi' : (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).ImmersedOn
      (I := 𝓘(ℝ, E)) (Icc t b') := fun x s hs => hi x s (hsub hs)
  have hestimate := leastArea_slope_le_of_minimizingDisk_and_boundaryIsotopy B' hdim gamma
    hgamma' hi' (fun s hs => hemb s (hsub hs)) t ⟨le_rfl, htb'⟩ hctr u sigma htrace
    hconformal hharmonic hmin Phi (hPhi.mono (Set.prod_mono (subset_univ _) hstrip)) hid
    (fun s hs => hboundary s (hstrip hs))
  have herr : (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).areaError
      B.family.metric (Icc t b') t =
      (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).areaError
      B.family.metric (Icc a b) t :=
    CurveMap.areaError_eq_of_subset _ _ hgamma hsub ⟨le_rfl, htb'.le⟩
      ((uniqueDiffOn_Icc htb') t ⟨le_rfl, htb'.le⟩)
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hestimate ε hε
  refine ⟨min δ (b' - t), lt_min hδ (sub_pos.mpr htb'), fun h hh _ => ?_⟩
  have hhδ : h < δ := hh.2.trans_le (min_le_left _ _)
  have hb' : t + h ≤ b' := by
    have hhl := hh.2.trans_le (min_le_right _ _)
    linarith
  have hres := hbound h ⟨hh.1, hhδ⟩ hb'
  change _ ≤ -2 * Real.pi - scalarMinimum B.family t *
    loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) t / 2 +
    (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).areaError
      B.family.metric (Icc t b') t + ε at hres
  rw [herr] at hres
  exact hres

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

end

section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

private theorem leastArea_slope_le_of_conformal_minimizing_disk_standardModel
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := 𝓘(ℝ, E)) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := 𝓘(ℝ, E)) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (t : ℝ) (ht : t ∈ Ico a b) (hctr : IsContractibleLoop (γ t))
    (u : Width.SmoothDisk (I := 𝓘(ℝ, E)) (Q := M))
    (sigma : Width.SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (Width.diskBoundary theta) = γ t (sigma.map theta))
    (hconformal : u.IsConformal (B.family.metric t)) (hharmonic : u.IsHarmonic (B.family.metric t))
    (hmin : ∀ v : Width.SmoothDisk (I := 𝓘(ℝ, E)) (Q := M),
      (∀ theta, v.map (Width.diskBoundary theta) = γ t theta) →
        Width.diskArea (B.family.metric t) u.map ≤ Width.diskArea (B.family.metric t) v.map) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) - loopFamilyLeastArea B.family.metric γ t) / h
        ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by
  classical
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  let gamma : ℝ → Width.RegularLoop 𝓘(ℝ, E) M := fun s =>
    if hs : s ∈ Icc a b then regularLoopSlice γ hγ s hs else regularLoopSlice γ hγ t htcc
  have hGamma (s : ℝ) (hs : s ∈ Icc a b) : (gamma s).toContinuousLoop = γ s := by
    simp only [gamma, dite_eq_left hs, regularLoopSlice]
  have hgamma : (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).SmoothOn
      (I := 𝓘(ℝ, E)) (Icc a b) := by
    apply hγ.congr
    intro p hp
    exact congrArg (fun f : ContinuousFreeLoop M => f (p.1 : Surgery.Topology.Circle)) (hGamma p.2
      hp.2)
  have hi' : (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).ImmersedOn
      (I := 𝓘(ℝ, E)) (Icc a b) := by
    intro x s hs
    have hX := CurveMap.X_eq_of_slice_eq (E := E)
      (c := curveOfLoopFamily (fun r => (gamma r).toContinuousLoop)) (c' := curveOfLoopFamily γ)
      (t := s) (fun theta => congrArg (fun f : ContinuousFreeLoop M => f theta) (hGamma s hs)) x
    rw [hX]
    exact hi x s hs
  have hemb' : ∀ s ∈ Icc a b, Topology.IsEmbedding (gamma s : Surgery.Topology.Circle → M) := by
    intro s hs
    rw [hGamma s hs]
    exact hemb s hs
  have hctr' : IsContractibleLoop (gamma t).toContinuousLoop := by rw [hGamma t htcc]; exact hctr
  have htrace' : ∀ theta, u.map (Width.diskBoundary theta) = gamma t (sigma.map theta) := by
    intro theta
    rw [hGamma t htcc]
    exact htrace theta
  have hmin' : ∀ v : Width.SmoothDisk (I := 𝓘(ℝ, E)) (Q := M),
      (∀ theta, v.map (Width.diskBoundary theta) = gamma t theta) →
        Width.diskArea (B.family.metric t) u.map ≤ Width.diskArea (B.family.metric t) v.map := by
    intro v hv
    apply hmin v
    intro theta
    have h := hv theta
    change v.map (Width.diskBoundary theta) = (gamma t).toContinuousLoop theta at h
    rwa [hGamma t htcc] at h
  have hest := Width.leastArea_slope_le_of_minimizingDisk B hdim gamma hgamma hi' hemb' t ht hctr'
    u sigma htrace' hconformal hharmonic hmin'
  have herr : (curveOfLoopFamily (fun s => (gamma s).toContinuousLoop)).areaError
      B.family.metric (Icc a b) t = (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t :=
    CurveMap.areaError_eq_of_eqOn B.family.metric
      (fun s hs theta => congrArg (fun f : ContinuousFreeLoop M => f theta) (hGamma s hs)) htcc
  have hA (s : ℝ) (hs : s ∈ Icc a b) :
      loopFamilyLeastArea B.family.metric (fun s => (gamma s).toContinuousLoop) s =
        loopFamilyLeastArea B.family.metric γ s := by
    simp only [loopFamilyLeastArea, hGamma s hs]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hest ε hε
  refine ⟨δ, hδ, fun h hh hb => ?_⟩
  have hth : t + h ∈ Icc a b := ⟨by linarith [ht.1, hh.1], hb⟩
  have hresult := hbound h hh hb
  rw [hA (t + h) hth, hA t htcc, herr] at hresult
  exact hresult

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
  [T2Space A] [CompactSpace A] [SigmaCompactSpace A]

omit [I.Boundaryless] [T2Space M] [CompactSpace M] [SigmaCompactSpace M]
  [CompactSpace A] [SigmaCompactSpace A] in
private theorem minimizing_comp_diffeomorph
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (γ : ContinuousFreeLoop M) (u : Width.SmoothDisk (I := I) (Q := M))
    (hmin : ∀ v : Width.SmoothDisk (I := I) (Q := M),
      (∀ theta, v.map (Width.diskBoundary theta) = γ theta) →
        Width.diskArea g u.map ≤ Width.diskArea g v.map) :
    ∀ v : Width.SmoothDisk (I := 𝓘(ℝ, E)) (Q := A),
      (∀ theta, v.map (Width.diskBoundary theta) = Φ (γ theta)) →
        Width.diskArea (Diffeomorph.pullbackMetricCross g Φ.symm)
          (Width.SmoothDisk.compDiffeomorph Φ u).map ≤
        Width.diskArea (Diffeomorph.pullbackMetricCross g Φ.symm) v.map := by
  intro v hv
  have htr : ∀ theta, (Width.SmoothDisk.compDiffeomorph Φ.symm v).map
      (Width.diskBoundary theta) = γ theta := by
    intro theta
    change Φ.symm (v.map (Width.diskBoundary theta)) = γ theta
    rw [hv, Φ.symm_apply_apply]
  have hm := hmin (Width.SmoothDisk.compDiffeomorph Φ.symm v) htr
  rw [Width.diskArea_pullbackMetricCross, Width.diskArea_pullbackMetricCross]
  have hu : (fun z : Width.Disk => Φ.symm ((Width.SmoothDisk.compDiffeomorph Φ u).map z)) =
      u.map := by
    funext z
    exact Φ.symm_apply_apply (u.map z)
  rw [hu]
  exact hm


omit [T2Space A] [CompactSpace A] [SigmaCompactSpace A] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem leastArea_slope_le_of_conformal_minimizing_disk
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (t : ℝ) (ht : t ∈ Ico a b) (hctr : IsContractibleLoop (γ t))
    (u : Width.SmoothDisk (I := I) (Q := M))
    (sigma : Width.SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (Width.diskBoundary theta) = γ t (sigma.map theta))
    (hconformal : u.IsConformal (B.family.metric t)) (hharmonic : u.IsHarmonic (B.family.metric t))
    (hmin : ∀ v : Width.SmoothDisk (I := I) (Q := M),
      (∀ theta, v.map (Width.diskBoundary theta) = γ t theta) →
        Width.diskArea (B.family.metric t) u.map ≤ Width.diskArea (B.family.metric t) v.map) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) - loopFamilyLeastArea B.family.metric γ t) / h
        ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by
  let c := DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := M)
    (ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace
    c
  let Φ : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ c.Q := c.equiv
  let γ' : ℝ → ContinuousFreeLoop c.Q :=
    fun s => (⟨Φ, Φ.continuous⟩ : C(M, c.Q)).comp (γ s)
  let u' : Width.SmoothDisk (I := 𝓘(ℝ, E)) (Q := c.Q) := Width.SmoothDisk.compDiffeomorph Φ u
  obtain ⟨B', hB'⟩ := exists_ricciBackground_pullback B Φ
  have hm (s : ℝ) : B'.family.metric s =
      Diffeomorph.pullbackMetricCross (B.family.metric s) Φ.symm :=
    congrArg (fun F : SolutionFamily (I := 𝓘(ℝ, E)) (M := c.Q) => F.metric s) hB'
  have hγ' : (curveOfLoopFamily γ').SmoothOn (I := 𝓘(ℝ, E)) (Icc a b) :=
    hγ.postcomposeDiffeomorph Φ
  have hi' : (curveOfLoopFamily γ').ImmersedOn (I := 𝓘(ℝ, E)) (Icc a b) :=
    CurveMap.ImmersedOn.postcomposeDiffeomorph hγ hi Φ
  have hemb' : ∀ s ∈ Icc a b, Topology.IsEmbedding (γ' s) := by
    intro s hs
    exact Φ.toHomeomorph.isEmbedding.comp (hemb s hs)
  have hctr' : IsContractibleLoop (γ' t) := hctr.postcompose ⟨Φ, Φ.continuous⟩
  have htrace' : ∀ theta, u'.map (Width.diskBoundary theta) = γ' t (sigma.map theta) := by
    intro theta
    change Φ (u.map (Width.diskBoundary theta)) = Φ (γ t (sigma.map theta))
    rw [htrace]
  have hconf' : u'.IsConformal (B'.family.metric t) := by
    rw [hm]
    exact Width.SmoothDisk.isConformal_comp_diffeomorph Φ (B.family.metric t) u hconformal
  have hharm' : u'.IsHarmonic (B'.family.metric t) := by
    rw [hm]
    exact Width.SmoothDisk.isHarmonic_comp_diffeomorph Φ (B.family.metric t) u hharmonic
  have hmin' : ∀ v : Width.SmoothDisk (I := 𝓘(ℝ, E)) (Q := c.Q),
      (∀ theta, v.map (Width.diskBoundary theta) = γ' t theta) →
        Width.diskArea (B'.family.metric t) u'.map ≤ Width.diskArea (B'.family.metric t) v.map := by
    rw [hm]
    exact minimizing_comp_diffeomorph (B.family.metric t) Φ (γ t) u hmin
  have hslope := leastArea_slope_le_of_conformal_minimizing_disk_standardModel B' hdim γ'
    hγ' hi' hemb' t ht hctr' u' sigma htrace' hconf' hharm' hmin'
  have hA (s : ℝ) : loopFamilyLeastArea B'.family.metric γ' s =
      loopFamilyLeastArea B.family.metric γ s := by
    rw [hB']
    exact loopFamilyLeastArea_postcomposeDiffeomorph B.family.metric Φ γ s
  have hscalar : scalarMinimum B'.family t = scalarMinimum B.family t := by
    rw [hB']
    exact scalarMinimum_pullback (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) Φ t
  have herr : (curveOfLoopFamily γ').areaError B'.family.metric (Icc a b) t =
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t := by
    rw [hB']
    exact (curveOfLoopFamily γ).areaError_postcomposeDiffeomorph Φ B.family.metric hγ hi t
      ⟨ht.1, ht.2.le⟩ ((uniqueDiffOn_Icc B.lt) t ⟨ht.1, ht.2.le⟩)
  simpa only [hA, hscalar, herr] using hslope

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
