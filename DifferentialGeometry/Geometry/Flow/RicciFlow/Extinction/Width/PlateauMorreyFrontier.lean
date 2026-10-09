import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonIntegrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauFluxComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HomogeneousRegularityBridge

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
  [hT2 : T2Space Q] [hCompact : CompactSpace Q]
  [hBoundary : I.Boundaryless] [hSigma : SigmaCompactSpace Q]

omit hT2 hCompact hBoundary hSigma in
structure PlateauSpanningFrontier (g : SmoothRiemannianMetric I Q)
    (gamma : ContinuousFreeLoop Q) where
  disk : SmoothDisk (I := I) (Q := Q)
  sigma : SmoothWeaklyMonotoneCircleMap
  trace : ∀ theta, disk.map (diskBoundary theta) = gamma (sigma.map theta)
  conformal : disk.IsConformal g
  harmonic : disk.IsHarmonic g
  minimizing : ∀ v : DiskCompetitor g gamma, diskArea g disk.map ≤ diskArea g v.1.map

variable {D : RealTimeInterval} {a b : ℝ}

omit hT2 hCompact hBoundary hSigma in
structure TransportedAreaFirstVariation (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b) (u : SmoothDisk (I := I) (Q := Q))
    (Phi : ℝ → Diffeomorph I I Q Q ∞) (hid : ∀ q, Phi t₀ q = q) : Prop where
  flux_integrable : IntervalIntegrable
    (u.boundaryFluxDensity (W.family.metric t₀)
      (u.isotopyVelocity Phi (Icc a b) t₀ hid)) volume 0 1
  hasDerivWithinAt : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
    ((1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z) -
      u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi (Icc a b) t₀ hid))
    (Icc a b) t₀

omit hSigma in
theorem rfs_plateau_upper_comparison_of_frontiers
    (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (himm : ∀ t ∈ Icc a b, ∀ x, loopVelocity (I := I) (gamma t).toContinuousLoop x ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t₀).toContinuousLoop)
    (F : PlateauSpanningFrontier (W.family.metric t₀) (gamma t₀).toContinuousLoop)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    (V : TransportedAreaFirstVariation W t₀ ht₀ F.disk Phi hid) :
    let Vv := F.disk.isotopyVelocity Phi (Icc a b) t₀ hid
    let metricTerm := F.disk.metricVariationDensity W.family.metric (Icc a b) t₀
    let variation := (1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension metricTerm z) -
        F.disk.boundaryFlux (W.family.metric t₀) Vv
    IntegrableOn (diskExtension metricTerm) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (F.disk.boundaryFluxDensity (W.family.metric t₀) Vv) volume 0 1 ∧
      (∀ t ∈ Icc a b,
        loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t ≤
          F.disk.transportedArea W.family.metric Phi t) ∧
      loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀ =
        F.disk.transportedArea W.family.metric Phi t₀ ∧
      HasDerivWithinAt (F.disk.transportedArea W.family.metric Phi) variation (Icc a b) t₀ ∧
      ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
        (loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) (t₀ + h) -
          loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀) / h ≤
            variation + epsilon := by
  classical
  let c : Topology.StandardModelCopy I Q E :=
    Topology.standardModelCopy (I := I) (M := Q) (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_boundaryFlux c W t₀ ht₀
    gamma hgamma hemb himm hctr F.disk F.sigma F.trace F.conformal F.harmonic F.minimizing
    Phi hPhi hid hboundary V.flux_integrable V.hasDerivWithinAt

omit hBoundary hT2 hCompact hSigma in
theorem slope_le_add_of_upper_bound
    {S L : ℝ → ℝ} {t₀ variation upper : ℝ} {a b : ℝ} (ht₀ : t₀ ∈ Ico a b)
    (hderiv : HasDerivWithinAt S variation (Icc a b) t₀) (hvar : variation ≤ upper)
    (hle : ∀ t ∈ Icc a b, L t ≤ S t) (heq : L t₀ = S t₀) :
    ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
      (L (t₀ + h) - L t₀) / h ≤ upper + epsilon := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdelta'⟩ :=
    slope_le_add_of_derivWithin_of_upper_contact ht₀ hderiv hle heq
      (epsilon / 2) (by linarith)
  refine ⟨delta, hdelta, fun h hh hb => ?_⟩
  have h := hdelta' h hh hb
  have hhalf : variation + epsilon / 2 ≤ upper + epsilon := by linarith
  linarith

omit hSigma in
theorem plateau_upper_slope_bound_of_frontiers
    (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (himm : ∀ t ∈ Icc a b, ∀ x, loopVelocity (I := I) (gamma t).toContinuousLoop x ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t₀).toContinuousLoop)
    (F : PlateauSpanningFrontier (W.family.metric t₀) (gamma t₀).toContinuousLoop)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    (V : TransportedAreaFirstVariation W t₀ ht₀ F.disk Phi hid) {upper : ℝ}
    (hupper : (1 / 2 : ℝ) *
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (F.disk.metricVariationDensity W.family.metric (Icc a b) t₀) z) -
        F.disk.boundaryFlux (W.family.metric t₀)
          (F.disk.isotopyVelocity Phi (Icc a b) t₀ hid) ≤ upper) :
    ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
      (loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) (t₀ + h) -
        loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀) / h ≤
          upper + epsilon := by
  have hmain := rfs_plateau_upper_comparison_of_frontiers W t₀ ht₀ gamma hgamma hemb himm hctr
    F Phi hPhi hid hboundary V
  dsimp only at hmain
  exact slope_le_add_of_upper_bound ht₀ hmain.2.2.2.2.1 hupper
    hmain.2.2.1 hmain.2.2.2.1

omit hSigma in
theorem rfs_plateau_upper_comparison_of_plateauSpanningFrontier
    (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (himm : ∀ t ∈ Icc a b, ∀ x, loopVelocity (I := I) (gamma t).toContinuousLoop x ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t₀).toContinuousLoop)
    (F : PlateauSpanningFrontier (W.family.metric t₀) (gamma t₀).toContinuousLoop)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta) :
    let Vv := F.disk.isotopyVelocity Phi (Icc a b) t₀ hid
    let metricTerm := F.disk.metricVariationDensity W.family.metric (Icc a b) t₀
    let variation := (1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension metricTerm z) -
        F.disk.boundaryFlux (W.family.metric t₀) Vv
    IntegrableOn (diskExtension metricTerm) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (F.disk.boundaryFluxDensity (W.family.metric t₀) Vv) volume 0 1 ∧
      (∀ t ∈ Icc a b,
        loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t ≤
          F.disk.transportedArea W.family.metric Phi t) ∧
      loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀ =
        F.disk.transportedArea W.family.metric Phi t₀ ∧
      HasDerivWithinAt (F.disk.transportedArea W.family.metric Phi) variation (Icc a b) t₀ ∧
      ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
        (loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) (t₀ + h) -
          loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀) / h ≤
            variation + epsilon := by
  classical
  let c : Topology.StandardModelCopy I Q E :=
    Topology.standardModelCopy (I := I) (M := Q) (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor c W t₀ ht₀ gamma hgamma hemb
    himm hctr F.disk F.sigma F.trace F.conformal F.harmonic F.minimizing Phi hPhi hid hboundary

omit hSigma in
theorem plateau_upper_slope_bound_of_plateauSpanningFrontier
    (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (himm : ∀ t ∈ Icc a b, ∀ x, loopVelocity (I := I) (gamma t).toContinuousLoop x ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t₀).toContinuousLoop)
    (F : PlateauSpanningFrontier (W.family.metric t₀) (gamma t₀).toContinuousLoop)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    {upper : ℝ}
    (hupper : (1 / 2 : ℝ) *
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (F.disk.metricVariationDensity W.family.metric (Icc a b) t₀) z) -
        F.disk.boundaryFlux (W.family.metric t₀)
          (F.disk.isotopyVelocity Phi (Icc a b) t₀ hid) ≤ upper) :
    ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
      (loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) (t₀ + h) -
        loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀) / h ≤
          upper + epsilon := by
  have hmain := rfs_plateau_upper_comparison_of_plateauSpanningFrontier W t₀ ht₀ gamma hgamma
    hemb himm hctr F Phi hPhi hid hboundary
  dsimp only at hmain
  exact slope_le_add_of_upper_bound ⟨ht₀.1.le, ht₀.2⟩ hmain.2.2.2.2.1 hupper
    hmain.2.2.1 hmain.2.2.2.1

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem density_family_at_constantDiskCompetitor (g : SmoothRiemannianMetric I Q) (q : Q) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j theta, (w j).map (diskBoundary theta) = constantLoops q theta) ∧
        Tendsto (fun j => diskArea g (w j).map) atTop
          (𝓝 (diskArea g (constantDiskCompetitor g q).1.map)) := by
  simpa only [constantDiskCompetitor] using
    exists_smoothDiskApproximation_of_constant (I := I) (Q := Q) g q

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem minimizing_disk_area_le_constant_competitor (g : SmoothRiemannianMetric I Q) (q : Q)
    (v : DiskCompetitor g (constantLoops q)) :
    diskArea g (⇑(SmoothDisk.const (I := I) (Q := Q) q).map) ≤ diskArea g v.1.map :=
  diskArea_const_le_diskCompetitor g q v

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
def SmoothWeaklyMonotoneCircleMap.id : SmoothWeaklyMonotoneCircleMap where
  map := ContinuousMap.id Surgery.Topology.Circle
  lift := fun t => t
  smooth_lift := contDiff_id
  monotone_lift := monotone_id
  increment := fun _ => rfl
  lift_eq := fun _ => rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] hT2 hCompact hBoundary hSigma in
theorem SmoothDisk.const_trace (q : Q) (sigma : SmoothWeaklyMonotoneCircleMap) :
    ∀ theta, (SmoothDisk.const (I := I) (Q := Q) q).map (diskBoundary theta) =
      constantLoops q (sigma.map theta) := by
  intro theta
  simp only [SmoothDisk.const]
  rfl

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem SmoothDisk.const_isConformal (g : SmoothRiemannianMetric I Q) (q : Q) :
    (SmoothDisk.const (I := I) (Q := Q) q).IsConformal g := by
  have hmap : diskExtension (⇑(SmoothDisk.const (I := I) (Q := Q) q).map) = fun _ => q := by
    funext w
    rw [diskExtension]
    split_ifs <;> rfl
  intro z
  have hzero (v : ℂ) : (SmoothDisk.const (I := I) (Q := Q) q).differential z v = 0 := by
    rw [SmoothDisk.differential, hmap]
    exact congrArg (fun (L : ℂ →L[ℝ] TangentSpace I q) => L v)
      (mfderivWithin_const (𝕜 := ℝ) (E := ℂ) (H := ℂ) (I := 𝓘(ℝ, ℂ)) (M := ℂ)
        (E' := E) (H' := H) (I' := I) (M' := Q) (s := Metric.closedBall (0 : ℂ) 1)
        (x := (z : ℂ)) (c := q))
  rw [hzero 1, hzero Complex.I]
  simp

theorem transportedAreaFirstVariation_refl
    (W : SmoothMetricWindow (I := I) (M := Q) D a b) (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b)
    (u : SmoothDisk (I := I) (Q := Q)) (hconf : u.IsConformal (W.family.metric t₀)) :
    TransportedAreaFirstVariation W t₀ ht₀ u (fun _ => Diffeomorph.refl I Q ∞)
      (fun _ => rfl) := by
  classical
  let c : Topology.StandardModelCopy I Q E :=
    Topology.standardModelCopy (I := I) (M := Q) (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  have hreg : D.regular ∈ 𝓝 t₀ :=
    D.regular_isOpen.mem_nhds (W.regular ⟨ht₀.1, ht₀.2.le⟩)
  obtain ⟨-, hderivAt⟩ := SmoothDisk.hasDerivAt_diskArea_metricFamily (hG := W.smooth) c u
    W.family.metric D.regular hreg hreg hconf
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
  have hfun : (fun z : ℂ => diskExtension
        (u.metricVariationDensity W.family.metric D.regular t₀) z) =
      fun z : ℂ => diskExtension
        (u.metricVariationDensity W.family.metric (Icc a b) t₀) z := by
    funext z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) 1
    · rw [diskExtension_coe (u.metricVariationDensity W.family.metric D.regular t₀) ⟨z, hz⟩,
        diskExtension_coe (u.metricVariationDensity W.family.metric (Icc a b) t₀) ⟨z, hz⟩]
      exact hdens ⟨z, hz⟩
    · have h1 : diskExtension (u.metricVariationDensity W.family.metric D.regular t₀) z =
          u.metricVariationDensity W.family.metric D.regular t₀ diskCenter := by
        rw [diskExtension]
        exact dite_eq_right hz
      have h2 : diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z =
          u.metricVariationDensity W.family.metric (Icc a b) t₀ diskCenter := by
        rw [diskExtension]
        exact dite_eq_right hz
      rw [h1, h2]
      exact hdens diskCenter
  have hderivAt' : HasDerivAt (fun t : ℝ => diskArea (W.family.metric t) u.map)
      ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z)) t₀ := by
    rw [← hfun]
    exact hderivAt
  have hV : u.isotopyVelocity (fun _ => Diffeomorph.refl I Q ∞) (Icc a b) t₀
      (fun _ => rfl) = fun _ => 0 := by
    funext z
    change mfderivWithin 𝓘(ℝ, ℝ) I
      (fun t : ℝ => (Diffeomorph.refl I Q ∞) (u.map z)) (Icc a b) t₀ 1 = 0
    have hc : (fun t : ℝ => (Diffeomorph.refl I Q ∞) (u.map z)) = fun _ => u.map z := by
      funext t
      simp [Diffeomorph.coe_refl]
    have h0 : mfderivWithin 𝓘(ℝ, ℝ) I (fun _ : ℝ => u.map z) (Icc a b) t₀ = 0 :=
      mfderivWithin_const (𝕜 := ℝ) (E := ℝ) (H := ℝ) (I := 𝓘(ℝ, ℝ)) (M := ℝ)
        (E' := E) (H' := H) (I' := I) (M' := Q) (s := Icc a b) (x := t₀) (c := u.map z)
    rw [hc, h0]
    rfl
  have hflux : u.boundaryFluxDensity (W.family.metric t₀)
      (u.isotopyVelocity (fun _ => Diffeomorph.refl I Q ∞) (Icc a b) t₀ (fun _ => rfl)) =
      fun _ => 0 := by
    funext x
    simp only [SmoothDisk.boundaryFluxDensity, hV]
    simp
  have hfluxzero : u.boundaryFlux (W.family.metric t₀)
      (u.isotopyVelocity (fun _ => Diffeomorph.refl I Q ∞) (Icc a b) t₀ (fun _ => rfl)) = 0 := by
    rw [SmoothDisk.boundaryFlux, hflux]
    simp
  have htrans : u.transportedArea W.family.metric (fun _ => Diffeomorph.refl I Q ∞) =
      fun t : ℝ => diskArea (W.family.metric t) u.map := by
    funext t
    rw [SmoothDisk.transportedArea]
    exact congrArg (fun f : Disk → Q => diskArea (W.family.metric t) f)
      (funext fun z => by
        simp [Diffeomorph.coe_refl])
  refine ⟨?_, ?_⟩
  · rw [hflux]
    exact IntervalIntegrable.zero
  · rw [htrans, hfluxzero, sub_zero]
    exact hderivAt'.hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
