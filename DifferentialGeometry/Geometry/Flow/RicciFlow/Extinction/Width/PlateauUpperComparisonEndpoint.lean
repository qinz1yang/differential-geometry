import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonVariation
import DifferentialGeometry.Topology.StandardModel

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem StandardModelCopy.compactSpace (c : StandardModelCopy I M F) [CompactSpace M] :
    CompactSpace c.Q :=
  c.equiv.toHomeomorph.compactSpace

end DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology CurveShortening

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem mfderivWithin_Icc_eq_mfderiv_of_mem_Ico {F : ℝ → Q} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico a b) (hd : MDifferentiableAt 𝓘(ℝ, ℝ) I F t₀) :
    mfderivWithin 𝓘(ℝ, ℝ) I F (Icc a b) t₀ = mfderiv 𝓘(ℝ, ℝ) I F t₀ := by
  have hab : a < b := lt_of_le_of_lt ht₀.1 ht₀.2
  have ht₀Icc : t₀ ∈ Icc a b := ⟨ht₀.1, ht₀.2.le⟩
  exact mfderivWithin_eq_mfderiv ((uniqueDiffOn_Icc hab) t₀ ht₀Icc).uniqueMDiffWithinAt hd

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem mfderivWithin_Icc_eq_mfderivWithin_of_isOpen {F : ℝ → Q} {a b t₀ : ℝ} {T : Set ℝ}
    (ht₀ : t₀ ∈ Ico a b) (hd : MDifferentiableAt 𝓘(ℝ, ℝ) I F t₀)
    (hTopen : IsOpen T) (hT₀ : t₀ ∈ T) :
    mfderivWithin 𝓘(ℝ, ℝ) I F (Icc a b) t₀ = mfderivWithin 𝓘(ℝ, ℝ) I F T t₀ :=
  (mfderivWithin_Icc_eq_mfderiv_of_mem_Ico ht₀ hd).trans
    (mfderivWithin_of_mem_nhds (hTopen.mem_nhds hT₀)).symm

end Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [hT2 : T2Space Q] [hCompact : CompactSpace Q]
  [hBoundary : I.Boundaryless] [hSigma : SigmaCompactSpace Q]

theorem rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
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
    (hmin : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.1.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (T : Set ℝ) (hTopen : IsOpen T) (hTsub : Icc a b ⊆ T)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ T))
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
  have ht₀Icc : t₀ ∈ Icc a b := ⟨ht₀.1, ht₀.2.le⟩
  have ht₀T : t₀ ∈ T := hTsub ht₀Icc
  have hreg : D.regular ∈ 𝓝 t₀ :=
    D.regular_isOpen.mem_nhds (W.regular ⟨ht₀.1, ht₀.2.le⟩)
  obtain ⟨hIntT, hFluxT, hDerivT⟩ :=
    SmoothDisk.hasDerivAt_transportedArea_isotopy_flux c W.smooth hreg u hconformal hharmonic
      hTopen ht₀T Phi hPhi hid
  have hdiff₁ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z (1 : ℂ))
        (u.differential z (1 : ℂ))) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z (1 : ℂ)) (u.differential z (1 : ℂ))).contDiffAt
      hreg).differentiableAt (by simp)
  have hdiff₂ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z Complex.I)
        (u.differential z Complex.I)) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z Complex.I) (u.differential z Complex.I)).contDiffAt
      hreg).differentiableAt (by simp)
  have hdensInt : (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric T t₀) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z := by
    refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    rw [show diskExtension (u.metricVariationDensity W.family.metric T t₀) z =
        u.metricVariationDensity W.family.metric T t₀ ⟨z, hz⟩ from dif_pos hz,
      show diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z =
        u.metricVariationDensity W.family.metric (Icc a b) t₀ ⟨z, hz⟩ from dif_pos hz]
    simp only [SmoothDisk.metricVariationDensity]
    split_ifs with hpos
    · rw [derivWithin_of_mem_nhds (hTopen.mem_nhds ht₀T),
        derivWithin_of_mem_nhds (hTopen.mem_nhds ht₀T),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₁ ⟨z, hz⟩),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₂ ⟨z, hz⟩)]
    · rfl
  have hvel : u.isotopyVelocity Phi (Icc a b) t₀ hid =
      u.isotopyVelocity Phi T t₀ hid := by
    funext z
    change mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ 1 =
      mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) T t₀ 1
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) t₀ := by
      have hbase : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
          (u.map z, t₀) :=
        hPhi.contMDiffAt ((isOpen_univ.prod hTopen).mem_nhds ⟨trivial, ht₀T⟩)
      exact (hbase.mdifferentiableAt (by simp)).comp t₀
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    exact congrArg (fun L => L 1)
      (mfderivWithin_Icc_eq_mfderivWithin_of_isOpen ht₀ hmdiff hTopen ht₀T)
  have hFluxIcc : IntervalIntegrable
      (u.boundaryFluxDensity (W.family.metric t₀)
        (u.isotopyVelocity Phi (Icc a b) t₀ hid)) volume 0 1 := by
    rw [hvel]
    exact hFluxT
  have hderivIcc : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
      ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z) -
        u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi (Icc a b) t₀ hid))
      (Icc a b) t₀ := by
    have hb : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
        ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity W.family.metric T t₀) z) -
          u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi T t₀ hid))
        (Icc a b) t₀ :=
      hDerivT.hasDerivWithinAt (s := Icc a b)
    convert hb using 1
    rw [hdensInt, hvel]
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv
    W t₀ ht₀ gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin Phi
    (hPhi.mono (Set.prod_mono Subset.rfl hTsub)) hid hboundary
    (SmoothDisk.integrableOn_diskExtension_metricVariationDensity c W ht₀ u hconformal)
    hFluxIcc hderivIcc

theorem rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
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
    (hdensity : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = gamma t₀ theta) ∧
          Tendsto (fun j => diskArea (W.family.metric t₀) (w j).map) atTop
            (𝓝 (diskArea (W.family.metric t₀) v.1.map)))
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
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q :=
    DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace c
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor c W t₀ ht₀ gamma hgamma
    hemb himm hctr u sigma htrace hconformal hharmonic
    (diskArea_le_of_minimizingSmoothDisk_of_density (W.family.metric t₀) (gamma t₀) u hmin
      hdensity)
    Phi hPhi hid hboundary

theorem rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density_of_openIsotopy
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
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
    (hdensity : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = gamma t₀ theta) ∧
          Tendsto (fun j => diskArea (W.family.metric t₀) (w j).map) atTop
            (𝓝 (diskArea (W.family.metric t₀) v.1.map)))
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (T : Set ℝ) (hTopen : IsOpen T) (hTsub : Icc a b ⊆ T)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ T))
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
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q :=
    DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace c
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy c W t₀ ht₀
    gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic
    (diskArea_le_of_minimizingSmoothDisk_of_density (W.family.metric t₀) (gamma t₀) u hmin
      hdensity)
    Phi T hTopen hTsub hPhi hid hboundary

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
