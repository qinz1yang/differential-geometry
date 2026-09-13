import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariationBoundaryFlux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LeastAreaAttainment
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.Comparison.CompactLowerBound

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

omit hBoundary hSigma in
theorem exists_edistOf_diffeomorph_le
    (g : SmoothRiemannianMetric I Q) (Phi : Q ≃ₘ⟮I, I⟯ Q) :
    ∃ L : ℝ≥0, ∀ x y : Q,
      riemannianEDistOf g (Phi x) (Phi y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y := by
  obtain ⟨c, hc, hlow⟩ := DifferentialGeometry.metric_lower_on (I := I) (M := Q)
    (K := Set.univ) isCompact_univ g (Diffeomorph.pullbackMetricCross g Phi)
  have hquad : ∀ x (v : TangentSpace I x),
      g.inner (Phi x) (mfderiv I I Phi x v) (mfderiv I I Phi x v) ≤
        c⁻¹ * g.inner x v v := by
    intro x v
    have h1 : c * g.inner (Phi x) (mfderiv I I Phi x v) (mfderiv I I Phi x v) ≤
        g.inner x v v := by
      have h := hlow x (Set.mem_univ x) v
      rwa [Diffeomorph.pullbackMetricCross_inner] at h
    calc g.inner (Phi x) (mfderiv I I Phi x v) (mfderiv I I Phi x v)
        = c⁻¹ * (c * g.inner (Phi x) (mfderiv I I Phi x v) (mfderiv I I Phi x v)) := by
          field_simp
      _ ≤ c⁻¹ * g.inner x v v := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc.le)
  refine ⟨Real.toNNReal (Real.sqrt c⁻¹), fun x y => ?_⟩
  have h := Metric.edistOf_le_of_quad_of_localDiffeomorph g g Phi Phi.isLocalDiffeomorph
    (inv_pos.mpr hc) hquad x y
  rw [← ENNReal.ofNNReal_toNNReal (Real.sqrt c⁻¹)] at h
  exact h

omit hSigma in
theorem SmoothDisk.exists_lipschitz_postcompose_diffeomorph
    (g : SmoothRiemannianMetric I Q) (u : SmoothDisk (I := I) (Q := Q))
    (Phi : Q ≃ₘ⟮I, I⟯ Q) :
    ∃ w : LipschitzDisk g,
      w.map = (⟨fun x => Phi x, Phi.continuous⟩ : C(Q, Q)).comp u.map := by
  obtain ⟨L, hL⟩ := exists_edistOf_diffeomorph_le g Phi
  obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
  refine ⟨LipschitzDisk.postcompose g g ⟨fun x => Phi x, Phi.continuous⟩ L hL ulip, ?_⟩
  simp only [LipschitzDisk.postcompose]
  rw [hulip]

variable {D : RealTimeInterval} {a b : ℝ}

omit hSigma in
theorem loopFamilyLeastArea_transportedArea_le
    (W : SmoothMetricWindow (I := I) (M := Q) D a b) (t₀ : ℝ)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (u : SmoothDisk (I := I) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) =
      (gamma t₀).toContinuousLoop (sigma.map theta))
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta,
      Phi t ((gamma t₀).toContinuousLoop theta) = (gamma t).toContinuousLoop theta)
    (t : ℝ) (ht : t ∈ Icc a b) :
    loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t ≤
      u.transportedArea W.family.metric Phi t := by
  have hγtsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift (gamma t).toContinuousLoop) := by
    have h := CurveMap.space_slice_contMDiffOn
      (curveOfLoopFamily (fun v => (gamma v).toContinuousLoop)) (Icc a b) hgamma t ht
    rwa [contMDiffOn_univ] at h
  let γt : RegularLoop I Q := regularLoopSlice (fun v => (gamma v).toContinuousLoop) hgamma t ht
  obtain ⟨L, hL⟩ := exists_edistOf_diffeomorph_le (W.family.metric t) (Phi t)
  obtain ⟨ulip, hulip⟩ := u.exists_lipschitz (W.family.metric t)
  let f : C(Q, Q) := ⟨fun x => Phi t x, (Phi t).continuous⟩
  let w : LipschitzDisk (W.family.metric t) :=
    LipschitzDisk.postcompose (W.family.metric t) (W.family.metric t) f L hL ulip
  have htracew : ∀ theta, w.map (diskBoundary theta) = γt.toContinuousLoop (sigma.map theta) := by
    intro theta
    have hu : ulip.map (diskBoundary theta) = u.map (diskBoundary theta) := by rw [hulip]
    change Phi t (ulip.map (diskBoundary theta)) = (gamma t).toContinuousLoop (sigma.map theta)
    rw [hu, htrace theta, hboundary t ht (sigma.map theta)]
  obtain ⟨v, hv⟩ := zero_area_trace_annulus (W.family.metric t) γt hγtsmooth sigma w htracew
  have hle : sInf (competitorAreas (W.family.metric t) ((gamma t).toContinuousLoop)) ≤
      diskArea (W.family.metric t) v.1.map :=
    csInf_le (competitorAreas_bddBelow _ _) ⟨v, rfl⟩
  rw [hv] at hle
  refine hle.trans_eq ?_
  rw [SmoothDisk.transportedArea]
  congr 1
  funext z
  have hu : ulip.map z = u.map z := by rw [hulip]
  change f (ulip.map z) = Phi t (u.map z)
  rw [hu]
  rfl

omit hSigma in
theorem transportedArea_at_base_eq_loopFamilyLeastArea
    (W : SmoothMetricWindow (I := I) (M := Q) D a b) (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (hctr : IsContractibleLoop (gamma t₀).toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) =
      (gamma t₀).toContinuousLoop (sigma.map theta))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = (gamma t₀).toContinuousLoop theta) →
        diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞) (hid : ∀ q, Phi t₀ q = q)
    (hdensity : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = (gamma t₀).toContinuousLoop theta) ∧
          Tendsto (fun j => diskArea (W.family.metric t₀) (w j).map) atTop
            (𝓝 (diskArea (W.family.metric t₀) v.1.map))) :
    loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀ =
      u.transportedArea W.family.metric Phi t₀ := by
  have ht₀Icc : t₀ ∈ Icc a b := ⟨ht₀.1, ht₀.2.le⟩
  have hγtsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift (gamma t₀).toContinuousLoop) := by
    have h := CurveMap.space_slice_contMDiffOn
      (curveOfLoopFamily (fun v => (gamma v).toContinuousLoop)) (Icc a b) hgamma t₀ ht₀Icc
    rwa [contMDiffOn_univ] at h
  let γt : RegularLoop I Q :=
    regularLoopSlice (fun v => (gamma v).toContinuousLoop) hgamma t₀ ht₀Icc
  have hatt := CurveShortening.diskArea_eq_leastArea_of_minimizingSmoothDisk
    (g := W.family.metric t₀) (γ := γt) hγtsmooth hctr u sigma htrace hmin hdensity
  have htrans : u.transportedArea W.family.metric Phi t₀ =
      diskArea (W.family.metric t₀) u.map := by
    rw [SmoothDisk.transportedArea]
    congr 1
    funext z
    exact hid (u.map z)
  rw [htrans, loopFamilyLeastArea_eq (W.family.metric) (fun v => (gamma v).toContinuousLoop) t₀
    hctr (γt.isLipschitz (W.family.metric t₀))]
  exact hatt.symm

omit hBoundary hT2 hCompact hSigma in
theorem slope_le_add_of_derivWithin_of_upper_contact
    {F L : ℝ → ℝ} {t₀ variation : ℝ} {a b : ℝ} (ht₀ : t₀ ∈ Ico a b)
    (hderiv : HasDerivWithinAt F variation (Icc a b) t₀)
    (hle : ∀ t ∈ Icc a b, L t ≤ F t) (heq : L t₀ = F t₀) :
    ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
      (L (t₀ + h) - L t₀) / h ≤ variation + epsilon := by
  intro epsilon hepsilon
  have hb : t₀ < b := ht₀.2
  have hslope : Tendsto (fun s => slope F t₀ s) (𝓝[>] t₀) (𝓝 variation) := by
    have h1 : Tendsto (slope F t₀) (𝓝[Icc a b \ {t₀}] t₀) (𝓝 variation) :=
      hasDerivWithinAt_iff_tendsto_slope.mp hderiv
    refine h1.mono_left ?_
    rw [nhdsWithin_le_iff]
    have hmem : (Ioi t₀ ∩ Iio b) ∈ 𝓝[>] t₀ :=
      inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hb))
    refine Filter.mem_of_superset hmem ?_
    intro s hs
    exact ⟨⟨le_trans ht₀.1 hs.1.le, hs.2.le⟩, ne_of_gt hs.1⟩
  obtain ⟨delta, hdelta, hdelta'⟩ := Metric.tendsto_nhdsWithin_nhds.mp hslope epsilon hepsilon
  refine ⟨delta, hdelta, fun h hh hb' => ?_⟩
  have hpos : 0 < h := hh.1
  have hmem : t₀ + h ∈ Ioi t₀ := by simpa using hpos
  have hdist : dist (t₀ + h) t₀ < delta := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hpos]
    exact hh.2
  have hlt : slope F t₀ (t₀ + h) < variation + epsilon := by
    have h := hdelta' hmem hdist
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).2]
  have hsl : slope F t₀ (t₀ + h) = (F (t₀ + h) - F t₀) / h := by
    rw [slope_def_field, add_sub_cancel_left]
  rw [hsl] at hlt
  have hnum : L (t₀ + h) ≤ F (t₀ + h) := hle (t₀ + h) ⟨by linarith [ht₀.1, hpos.le], hb'⟩
  have hdiv : (L (t₀ + h) - L t₀) / h ≤ (F (t₀ + h) - F t₀) / h := by
    apply div_le_div_of_nonneg_right _ hpos.le
    rw [heq]
    linarith
  exact hdiv.trans hlt.le

omit hSigma in
theorem rfs_plateau_upper_comparison_of_smoothDiskDensity_and_transportedAreaDeriv
    (W : SmoothMetricWindow (I := I) (M := Q) D a b)
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
    (hdensity : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = gamma t₀ theta) ∧
          Tendsto (fun j => diskArea (W.family.metric t₀) (w j).map) atTop
            (𝓝 (diskArea (W.family.metric t₀) v.1.map)))
    (hintDensity : IntegrableOn
      (diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀))
      (Metric.closedBall (0 : ℂ) 1))
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
            variation + epsilon := by
  let _ := hemb
  let _ := himm
  let _ := hconformal
  let _ := hharmonic
  let _ := hPhi
  dsimp only
  refine ⟨hintDensity, hintFlux, ?_, ?_, hderiv, ?_⟩
  · intro t ht
    exact loopFamilyLeastArea_transportedArea_le W t₀ gamma hgamma u sigma htrace Phi
      (fun t ht theta => hboundary t ht theta) t ht
  · exact transportedArea_at_base_eq_loopFamilyLeastArea W t₀ ht₀ gamma hgamma hctr u sigma
      htrace hmin Phi hid hdensity
  · refine slope_le_add_of_derivWithin_of_upper_contact ht₀ hderiv ?_ ?_
    · intro t ht
      exact loopFamilyLeastArea_transportedArea_le W t₀ gamma hgamma u sigma htrace Phi
        (fun t ht theta => hboundary t ht theta) t ht
    · exact transportedArea_at_base_eq_loopFamilyLeastArea W t₀ ht₀ gamma hgamma hctr u sigma
        htrace hmin Phi hid hdensity

omit hBoundary hT2 hCompact in
def SmoothDisk.const (q : Q) : SmoothDisk (I := I) (Q := Q) where
  map := ⟨fun _ => q, continuous_const⟩
  smooth z := ⟨{
    map := fun _ => q
    domain := Set.univ
    isOpen_domain := isOpen_univ
    mem_domain := Set.mem_univ z
    smooth := contMDiffOn_const
    agrees := fun w hw => by simp [diskExtension, hw.2] }⟩

omit [FiniteDimensional ℝ E] hBoundary hT2 hCompact hSigma in
theorem exists_smoothDiskApproximation_of_trace
    (g : SmoothRiemannianMetric I Q) (gamma : RegularLoop I Q)
    (u : SmoothDisk (I := I) (Q := Q))
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop theta) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j theta, (w j).map (diskBoundary theta) = gamma.toContinuousLoop theta) ∧
        Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g u.map)) :=
  ⟨fun _ => u, fun _ theta => htrace theta, tendsto_const_nhds⟩

omit [FiniteDimensional ℝ E] hBoundary hT2 hCompact hSigma in
theorem exists_smoothDiskApproximation_of_constant
    (g : SmoothRiemannianMetric I Q) (q : Q) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j theta, (w j).map (diskBoundary theta) = constantLoops q theta) ∧
        Tendsto (fun j => diskArea g (w j).map) atTop
          (𝓝 (diskArea g (constantLipschitzDisk g q).map)) := by
  refine ⟨fun _ => SmoothDisk.const (I := I) (Q := Q) q, ?_, ?_⟩
  · intro j theta
    simp only [SmoothDisk.const]
    rfl
  · have hconst : diskArea g (fun _ : Disk => q) = 0 := diskArea_const g q
    have h1 : diskArea g (⇑(SmoothDisk.const (I := I) (Q := Q) q).map) = 0 := by
      rw [show (⇑(SmoothDisk.const (I := I) (Q := Q) q).map : Disk → Q) =
        (fun _ : Disk => q) from rfl]
      exact hconst
    have h2 : diskArea g (⇑(constantLipschitzDisk g q).map) = 0 := by
      have hfun : (⇑(constantLipschitzDisk g q).map : Disk → Q) = fun _ : Disk => q := by
        funext z
        rfl
      rw [hfun]
      exact hconst
    change Tendsto (fun _ : ℕ => diskArea g (⇑(SmoothDisk.const (I := I) (Q := Q) q).map))
      atTop (𝓝 (diskArea g (⇑(constantLipschitzDisk g q).map)))
    rw [h1, h2]
    exact tendsto_const_nhds

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
