import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauMorreyFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauDensityTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauDiskDensityEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.InteriorConstDiskWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ConformalDiskFromMorrey

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem smooth_disk_exact_density_iff_plateau_disk_density (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) :
    (∀ v : DiskCompetitor g γ.toContinuousLoop,
        ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
          (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
            Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map))) ↔
      PlateauDiskDensity (I := I) (Q := Q) g γ.toContinuousLoop :=
  Iff.rfl

section StandardModelDensity

variable [FiniteDimensional ℝ E]

theorem smooth_exact_disk_density_of_smooth_disk_area_density
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E)
    [T2Space Q]
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : Geometry.SmoothDiskAreaDensity (E := E)
      (Diffeomorph.pullbackMetricCross g c.equiv.symm)
      ((⟨fun q => c.equiv q, c.equiv.continuous⟩ : C(Q, c.Q)).comp γ.toContinuousLoop)) :
    ∀ v : DiskCompetitor g γ.toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
          Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map)) :=
  smooth_exact_disk_density_of_standardModelCopy c g γ
    (plateauDiskDensity_of_smoothDiskAreaDensity _ _ h)

omit [FiniteDimensional ℝ E] in
theorem smooth_disk_exact_density_of_subsingleton [Subsingleton Q] [Nonempty Q]
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q) :
    ∀ v : DiskCompetitor g γ.toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
          Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map)) :=
  (smooth_disk_exact_density_iff_plateau_disk_density g γ).mpr
    (plateauDiskDensity_of_subsingleton g γ.toContinuousLoop)

end StandardModelDensity

theorem rfs_plateau_upper_comparison_of_plateau_disk_density_and_first_variation
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q] [SigmaCompactSpace Q]
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
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    (hdensity : PlateauDiskDensity (I := I) (Q := Q) (W.family.metric t₀)
      (gamma t₀).toContinuousLoop)
    (V : TransportedAreaFirstVariation W t₀ ht₀ u Phi hid) :
    let Vv := u.isotopyVelocity Phi (Icc a b) t₀ hid
    let metricTerm := u.metricVariationDensity W.family.metric (Icc a b) t₀
    let variation := (1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension metricTerm z) -
        u.boundaryFlux (W.family.metric t₀) Vv
    IntegrableOn (diskExtension metricTerm) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryFluxDensity (W.family.metric t₀) Vv) volume 0 1 ∧
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
  classical
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q :=
    DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace c
  exact rfs_plateau_upper_comparison_of_smoothDiskDensity_and_transportedAreaDeriv W t₀ ht₀
    gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin Phi hPhi hid hboundary
    hdensity
    (SmoothDisk.integrableOn_diskExtension_metricVariationDensity c W ht₀ u hconformal)
    V.flux_integrable V.hasDerivWithinAt

theorem transported_area_first_variation_of_isOpen_isotopy
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q] [SigmaCompactSpace Q]
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (u : SmoothDisk (I := I) (Q := Q)) (hconformal : u.IsConformal (W.family.metric t₀))
    (hharmonic : u.IsHarmonic (W.family.metric t₀))
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (T : Set ℝ) (hTopen : IsOpen T) (hTsub : Icc a b ⊆ T)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ T))
    (hid : ∀ q, Phi t₀ q = q) :
    TransportedAreaFirstVariation W t₀ ⟨ht₀.1.le, ht₀.2⟩ u Phi hid := by
  classical
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q :=
    DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace c
  have ht₀Ico : t₀ ∈ Ico a b := ⟨ht₀.1.le, ht₀.2⟩
  have ht₀T : t₀ ∈ T := hTsub ⟨ht₀.1.le, ht₀.2.le⟩
  have hreg : D.regular ∈ 𝓝 t₀ :=
    D.regular_isOpen.mem_nhds (W.regular ⟨ht₀.1.le, ht₀.2.le⟩)
  obtain ⟨-, hFluxT, hDerivT⟩ :=
    SmoothDisk.hasDerivAt_transportedArea_isotopy_flux c W.smooth hreg u hconformal hharmonic
      hTopen ht₀T Phi hPhi hid
  have hvel : u.isotopyVelocity Phi (Icc a b) t₀ hid =
      u.isotopyVelocity Phi T t₀ hid := by
    funext z
    change mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ 1 =
      mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) T t₀ 1
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr ⟨ht₀.1, ht₀.2⟩),
      mfderivWithin_of_mem_nhds (hTopen.mem_nhds ht₀T)]
  have hdiff₁ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z (1 : ℂ))
        (u.differential z (1 : ℂ))) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z (1 : ℂ))
      (u.differential z (1 : ℂ))).contDiffAt hreg).differentiableAt (by simp)
  have hdiff₂ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z Complex.I)
        (u.differential z Complex.I)) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z Complex.I)
      (u.differential z Complex.I)).contDiffAt hreg).differentiableAt (by simp)
  have hdensInt : (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric T t₀) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z := by
    refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    rw [show diskExtension (u.metricVariationDensity W.family.metric T t₀) z =
        u.metricVariationDensity W.family.metric T t₀ ⟨z, hz⟩ from dite_eq_left hz,
      show diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z =
        u.metricVariationDensity W.family.metric (Icc a b) t₀ ⟨z, hz⟩ from dite_eq_left hz]
    simp only [SmoothDisk.metricVariationDensity]
    split_ifs with hpos
    · rw [derivWithin_of_mem_nhds (hTopen.mem_nhds ht₀T),
        derivWithin_of_mem_nhds (hTopen.mem_nhds ht₀T),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀Ico (hdiff₁ ⟨z, hz⟩),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀Ico (hdiff₂ ⟨z, hz⟩)]
    · rfl
  refine ⟨?_, ?_⟩
  · rw [hvel]
    exact hFluxT
  · have hb : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
        ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity W.family.metric T t₀) z) -
          u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi T t₀ hid))
        (Icc a b) t₀ := hDerivT.hasDerivWithinAt
    convert hb using 1
    rw [hdensInt, hvel]

theorem classical_plateau_morrey_iff_has_conformal_minimizing_interior_disk
    [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q) :
    (∃ u : InteriorSmoothDisk (I := I) (Q := Q),
      u.IsConformal g ∧ u.IsHarmonic g ∧
      IsSignedWeaklyMonotoneTrace u.map γ.toContinuousLoop ∧
      IntegrableOn (diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ w : LipschitzDisk g, (∀ theta, w.map (diskBoundary theta) = γ theta) →
        diskArea g u.map ≤ diskArea g w.map) ∧
      ∀ w : SmoothDisk (I := I) (Q := Q), (∀ theta, w.map (diskBoundary theta) = γ theta) →
        diskArea g u.map ≤ diskArea g w.map) ↔
      HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ :=
  Iff.rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
