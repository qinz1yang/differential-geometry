import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonDiskAreaApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauDiskDensitySmoothTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ConformalDiskFromMorrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauFrontierMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.MinimalDiskAreaVariationReduction

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [hT2 : T2Space Q] [hCompact : CompactSpace Q]
  [hBoundary : I.Boundaryless] [hSigma : SigmaCompactSpace Q]

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem exists_smoothDisk_sequence_tendsto_area_of_minimizingDiskCompetitor
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (v : DiskCompetitor g γ.toContinuousLoop)
    (hupper : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ w : SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (diskBoundary theta) = γ theta) ∧
          diskArea g w.map ≤ diskArea g v.1.map + epsilon)
    (hmin : ∀ u : SmoothDisk (I := I) (Q := Q),
      (∀ theta, u.map (diskBoundary theta) = γ theta) →
        diskArea g v.1.map ≤ diskArea g u.map) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j theta, (w j).map (diskBoundary theta) = γ theta) ∧
        Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map)) := by
  choose w hw hle using fun j : ℕ => hupper (1 / ((j : ℝ) + 1)) (by positivity)
  have hlow (j : ℕ) : diskArea g v.1.map ≤ diskArea g (w j).map := hmin (w j) (hw j)
  have hub (j : ℕ) : diskArea g (w j).map ≤ diskArea g v.1.map + 1 / ((j : ℝ) + 1) := hle j
  refine ⟨w, hw, ?_⟩
  have hnorm : Tendsto (fun j : ℕ => ‖diskArea g (w j).map - diskArea g v.1.map‖)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : diskArea g (w j).map - diskArea g v.1.map ≤ 1 / ((j : ℝ) + 1) := by
      linarith [hub j]
    have h2 : diskArea g v.1.map - diskArea g (w j).map ≤ 1 / ((j : ℝ) + 1) := by
      have hnonneg : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) := by positivity
      linarith [hlow j]
    rw [norm_norm, Real.norm_eq_abs]
    exact abs_sub_le_iff.mpr ⟨h1, h2⟩
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hnorm

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem smoothDiskDensityAt_iff_areaUpperApproximation_of_minimizingDiskCompetitor
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (v : DiskCompetitor g γ.toContinuousLoop)
    (hmin : ∀ u : SmoothDisk (I := I) (Q := Q),
      (∀ theta, u.map (diskBoundary theta) = γ theta) →
        diskArea g v.1.map ≤ diskArea g u.map) :
    (∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = γ theta) ∧
          Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map))) ↔
      (∀ epsilon : ℝ, 0 < epsilon →
        ∃ w : SmoothDisk (I := I) (Q := Q),
          (∀ theta, w.map (diskBoundary theta) = γ theta) ∧
            diskArea g w.map ≤ diskArea g v.1.map + epsilon) := by
  constructor
  · intro h epsilon hepsilon
    obtain ⟨w, hw, ht⟩ := h
    obtain ⟨j, hj⟩ := (ht.eventually (Metric.ball_mem_nhds _ hepsilon)).exists
    refine ⟨w j, hw j, ?_⟩
    rw [Real.dist_eq] at hj
    linarith [(abs_lt.mp hj).2]
  · intro h
    exact exists_smoothDisk_sequence_tendsto_area_of_minimizingDiskCompetitor g γ v h hmin

omit hSigma in
theorem exists_smoothDisk_sequence_tendsto_area_of_diskArea_eq_leastArea
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hupper : PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q) g γ.toContinuousLoop)
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (v : DiskCompetitor g γ.toContinuousLoop)
    (hv : diskArea g v.1.map = leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g)) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j theta, (w j).map (diskBoundary theta) = γ theta) ∧
        Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map)) := by
  refine exists_smoothDisk_sequence_tendsto_area_of_minimizingDiskCompetitor g γ v
    (fun epsilon hepsilon => hupper v epsilon hepsilon) ?_
  intro u hu
  rw [hv]
  obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
  simpa only [hulip] using leastArea_le_competitor g γ.toContinuousLoop hctr (γ.isLipschitz g)
    ⟨ulip, fun theta => by rw [hulip]; exact hu theta⟩

omit hSigma in
theorem diskArea_eq_leastArea_of_minimizingSmoothDisk_and_areaUpperApproximation
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (hupper : PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q) g γ.toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = γ theta) →
        diskArea g u.map ≤ diskArea g v.map) :
    diskArea g u.map = leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
    have hbound : diskArea g u.map - epsilon ≤
        leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
      apply le_csInf (competitorAreas_nonempty g γ.toContinuousLoop hctr (γ.isLipschitz g))
      rintro _ ⟨v, rfl⟩
      obtain ⟨w, hw, hle⟩ := hupper v (epsilon / 2) (by linarith)
      linarith [hmin w hw]
    linarith
  · obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
    have htracelip : ∀ theta, ulip.map (diskBoundary theta) =
        γ.toContinuousLoop (sigma.map theta) := by
      simpa only [hulip] using htrace
    obtain ⟨v, hv⟩ := zero_area_trace_annulus g γ hγ sigma ulip htracelip
    have hle := leastArea_le_competitor g γ.toContinuousLoop hctr (γ.isLipschitz g) v
    simpa only [hv, hulip] using hle

omit hT2 hCompact hBoundary hSigma in
theorem minimizingConformalInteriorDisk_of_smoothInteriorDisk_of_areaUpperApproximation
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hupper : PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q) g γ.toContinuousLoop)
    (h : HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ) :
    HasMinimizingConformalInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hminS⟩ := h
  refine ⟨u, hconf, hharm, htrace, hfinite, fun v => ?_⟩
  refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
  obtain ⟨w, hw, hle⟩ := hupper v epsilon hepsilon
  exact (hminS w hw).trans hle

omit hSigma in
theorem hasConformalMinimizingInteriorDisk_of_smoothInteriorDisk_of_areaUpperApproximation
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hupper : PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q) g γ.toContinuousLoop)
    (h : HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ) :
    HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hmin⟩ :=
    minimizingConformalInteriorDisk_of_smoothInteriorDisk_of_areaUpperApproximation g γ hupper h
  exact ⟨u, hconf, hharm, htrace, hfinite,
    lipschitzDisk_minimization_of_diskCompetitor_minimization g hmin,
    smoothDisk_minimization_of_lipschitzDisk_minimization g
      (lipschitzDisk_minimization_of_diskCompetitor_minimization g hmin)⟩

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem not_plateauDiskDensityAreaUpperApproximation_chordLengthLoop :
    ¬ PlateauDiskDensityAreaUpperApproximation (I := 𝓘(ℝ, ℝ)) (Q := ℝ)
        (Geometry.standardEuclideanMetric ℝ) chordLengthLoop := by
  intro h
  obtain ⟨w, hw, -⟩ := h chordLengthDiskCompetitor 1 (by norm_num)
  exact not_contMDiff_loopLift_chordLengthLoop
    ((SmoothDisk.contMDiff_trace w).congr fun t =>
      (hw (t : Surgery.Topology.Circle)).symm)

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]

theorem diskArea_eq_leastArea_of_minimizingSmoothDisk_of_areaUpperApproximation
    (g : SmoothRiemannianMetric I M) (γ : Width.RegularLoop I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift γ.toContinuousLoop))
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (u : Width.SmoothDisk (I := I) (Q := M)) (sigma : Width.SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta : Surgery.Topology.Circle,
      u.map (Width.diskBoundary theta) = γ.toContinuousLoop (sigma.map theta))
    (hmin : ∀ v : Width.SmoothDisk (I := I) (Q := M),
      (∀ theta : Surgery.Topology.Circle,
        v.map (Width.diskBoundary theta) = γ.toContinuousLoop theta) →
        Width.diskArea g u.map ≤ Width.diskArea g v.map)
    (hupper : Width.PlateauDiskDensityAreaUpperApproximation (I := I) (Q := M) g
      γ.toContinuousLoop) :
    Width.diskArea g u.map = Width.leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
    have hbound : Width.diskArea g u.map - epsilon ≤
        Width.leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
      apply le_csInf (Width.competitorAreas_nonempty g γ.toContinuousLoop hctr
        (γ.isLipschitz g))
      rintro _ ⟨v, rfl⟩
      obtain ⟨w, hw, hle⟩ := hupper v (epsilon / 2) (by linarith)
      linarith [hmin w hw]
    linarith
  · obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
    have htracelip : ∀ theta, ulip.map (Width.diskBoundary theta) =
        γ.toContinuousLoop (sigma.map theta) := by
      simpa only [hulip] using htrace
    obtain ⟨v, hv⟩ := Width.zero_area_trace_annulus g γ hγ sigma ulip htracelip
    have hle := Width.leastArea_le_competitor g γ.toContinuousLoop hctr (γ.isLipschitz g) v
    simpa only [hv, hulip] using hle

theorem exists_diskCompetitor_area_eq_leastArea_of_minimizingSmoothDisk_and_areaUpperApproximation
    (g : SmoothRiemannianMetric I M) (γ : Width.RegularLoop I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift γ.toContinuousLoop))
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (u : Width.SmoothDisk (I := I) (Q := M)) (sigma : Width.SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta : Surgery.Topology.Circle,
      u.map (Width.diskBoundary theta) = γ.toContinuousLoop (sigma.map theta))
    (hmin : ∀ v : Width.SmoothDisk (I := I) (Q := M),
      (∀ theta : Surgery.Topology.Circle,
        v.map (Width.diskBoundary theta) = γ.toContinuousLoop theta) →
        Width.diskArea g u.map ≤ Width.diskArea g v.map)
    (hupper : Width.PlateauDiskDensityAreaUpperApproximation (I := I) (Q := M) g
      γ.toContinuousLoop) :
    ∃ w : Width.DiskCompetitor g γ.toContinuousLoop,
      Width.diskArea g w.1.map =
        Width.leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  have hA := diskArea_eq_leastArea_of_minimizingSmoothDisk_of_areaUpperApproximation g γ hγ hctr
    u sigma htrace hmin hupper
  obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
  have htracelip : ∀ theta, ulip.map (Width.diskBoundary theta) =
      γ.toContinuousLoop (sigma.map theta) := by
    simpa only [hulip] using htrace
  obtain ⟨v, hv⟩ := Width.zero_area_trace_annulus g γ hγ sigma ulip htracelip
  exact ⟨v, by rw [hv, hulip]; exact hA⟩

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_diskCompetitor_diskArea_eq_loopFamilyLeastArea_of_areaUpperApproximation
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hslice : ∀ t ∈ Ico a b, ∃ (u : Width.SmoothDisk (I := I) (Q := M))
        (sigma : Width.SmoothWeaklyMonotoneCircleMap),
      (∀ θ : Surgery.Topology.Circle,
        u.map (Width.diskBoundary θ) = γ t (sigma.map θ)) ∧
      ∀ v : Width.SmoothDisk (I := I) (Q := M),
        (∀ θ : Surgery.Topology.Circle, v.map (Width.diskBoundary θ) = γ t θ) →
          Width.diskArea (B.family.metric t) u.map ≤
            Width.diskArea (B.family.metric t) v.map)
    (hupper : ∀ t ∈ Ico a b,
      Width.PlateauDiskDensityAreaUpperApproximation (I := I) (Q := M)
        (B.family.metric t) (γ t)) :
    ∀ t ∈ Ico a b, ∃ u : Width.DiskCompetitor (B.family.metric t) (γ t),
      Width.diskArea (B.family.metric t) u.1.map = loopFamilyLeastArea B.family.metric γ t := by
  intro t ht
  have htIcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  obtain ⟨u, sigma, htrace, hmin⟩ := hslice t ht
  have hγt := (curveOfLoopFamily γ).smooth_slice hγ htIcc
  obtain ⟨w, hw⟩ :=
    exists_diskCompetitor_area_eq_leastArea_of_minimizingSmoothDisk_and_areaUpperApproximation
      (g := B.family.metric t) (γ := regularLoopSlice γ hγ t htIcc) hγt (hctr t htIcc) u sigma
      htrace hmin (hupper t ht)
  refine ⟨w, ?_⟩
  rw [loopFamilyLeastArea_eq_regularLeastAreaSlice B.family.metric γ hγ hctr t htIcc]
  exact hw

theorem curveShorteningLeastAreaAttainment_of_areaUpperApproximation
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hslice : ∀ t ∈ Ico a b, ∃ (u : Width.SmoothDisk (I := I) (Q := M))
        (sigma : Width.SmoothWeaklyMonotoneCircleMap),
      (∀ θ : Surgery.Topology.Circle,
        u.map (Width.diskBoundary θ) = γ t (sigma.map θ)) ∧
      ∀ v : Width.SmoothDisk (I := I) (Q := M),
        (∀ θ : Surgery.Topology.Circle, v.map (Width.diskBoundary θ) = γ t θ) →
          Width.diskArea (B.family.metric t) u.map ≤
            Width.diskArea (B.family.metric t) v.map)
    (hupper : ∀ t ∈ Ico a b,
      Width.PlateauDiskDensityAreaUpperApproximation (I := I) (Q := M)
        (B.family.metric t) (γ t)) :
    CurveShorteningLeastAreaAttainment (I := I) (M := M) B γ :=
  exists_diskCompetitor_diskArea_eq_loopFamilyLeastArea_of_areaUpperApproximation B γ hγ hctr
    hslice hupper

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
