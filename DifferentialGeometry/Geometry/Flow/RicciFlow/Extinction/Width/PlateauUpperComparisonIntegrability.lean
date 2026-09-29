import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskAreaMetricFirstVariation

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem derivWithin_Icc_eq_deriv_of_mem_Ico {F : ℝ → ℝ} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico a b) (hd : DifferentiableAt ℝ F t₀) :
    derivWithin F (Icc a b) t₀ = deriv F t₀ := by
  have hset : Icc a b = Ici a ∩ Iic b := by
    ext x
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [hset]
  rw [derivWithin_inter (s := Set.Ici a) (t := Set.Iic b) (Iic_mem_nhds ht₀.2)]
  by_cases h : a < t₀
  · exact derivWithin_of_mem_nhds (Ici_mem_nhds h)
  · have hta : t₀ = a := le_antisymm (not_lt.mp h) ht₀.1
    have hd' : DifferentiableAt ℝ F a := hta ▸ hd
    rw [hta]
    exact hd'.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici a)

variable [hT2 : T2Space Q] [hCompact : CompactSpace Q] [hSigma : SigmaCompactSpace Q]
  [hBoundary : I.Boundaryless]

omit hSigma in
theorem SmoothDisk.integrableOn_diskExtension_metricVariationDensity
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    {D : RealTimeInterval} {a b t₀ : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (ht₀ : t₀ ∈ Ico a b) (u : SmoothDisk (I := I) (Q := Q))
    (hconf : u.IsConformal (W.family.metric t₀)) :
    IntegrableOn (diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀))
      (Metric.closedBall (0 : ℂ) 1) := by
  have hreg : D.regular ∈ 𝓝 t₀ :=
    D.regular_isOpen.mem_nhds (W.regular ⟨ht₀.1, ht₀.2.le⟩)
  have hInt : IntegrableOn
      (diskExtension (u.metricVariationDensity W.family.metric D.regular t₀))
      (Metric.closedBall (0 : ℂ) 1) :=
    (SmoothDisk.hasDerivAt_diskArea_metricFamily (I := I) (Q := Q) (hG := W.smooth)
      c u W.family.metric D.regular hreg hreg hconf).1
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
  have hdens (z : Disk) : u.metricVariationDensity W.family.metric D.regular t₀ z =
      u.metricVariationDensity W.family.metric (Icc a b) t₀ z := by
    simp only [SmoothDisk.metricVariationDensity]
    split_ifs with hpos
    · rw [derivWithin_of_mem_nhds hreg, derivWithin_of_mem_nhds hreg,
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₁ z),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₂ z)]
    · rfl
  refine hInt.congr_fun ?_ measurableSet_closedBall
  intro z hz
  rw [show diskExtension (u.metricVariationDensity W.family.metric D.regular t₀) z =
      u.metricVariationDensity W.family.metric D.regular t₀ ⟨z, hz⟩ from dite_eq_left hz,
    show diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z =
      u.metricVariationDensity W.family.metric (Icc a b) t₀ ⟨z, hz⟩ from dite_eq_left hz]
  exact hdens ⟨z, hz⟩

omit hSigma in
theorem rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_boundaryFlux
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
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    (hintFlux : IntervalIntegrable
      (u.boundaryFluxDensity (W.family.metric t₀)
        (u.isotopyVelocity Phi (Icc a b) t₀ hid)) volume 0 1)
    (hderiv : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
      ((1 / 2 : ℝ) *
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z) -
        u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi (Icc a b) t₀ hid))
      (Icc a b) t₀) :
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
            variation + epsilon :=
  rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv
    W t₀ ht₀ gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin Phi hPhi hid
    hboundary (SmoothDisk.integrableOn_diskExtension_metricVariationDensity c W ht₀ u hconformal)
    hintFlux hderiv

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
