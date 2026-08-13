import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingLogTail
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeMeasure
import DifferentialGeometry.Analysis.Integration.Measure.CompactVolumeEquiv

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [I.Boundaryless] in
theorem localizedSpacetimeMeasure_real_superlevel_le_evolvingLocalizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (cutoff : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b level t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        C • riemannianMeasureFamily (I := I) (M := M) g t) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | level < u z.1 z.2} ≤
      C.toReal * ∫ t in a..b,
        evolvingLocalizedSuperlevelMass
          (I := I) (M := M) g cutoff.toFun u t level := by
  let fixed : ℝ → ℝ := fun t =>
    ∫ x in {x : M | level < u t x}, cutoff.toFun x ^ 2
      ∂(riemannianVolumeMeasure (I := I) (M := M) q)
  let moving : ℝ → ℝ := fun t =>
    evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g cutoff.toFun u t level
  have hfixed_int : IntervalIntegrable fixed volume a b := by
    simpa only [fixed, localizedSuperlevelMass, smoothScalarSlice_toFun] using
      intervalIntegrable_localizedSuperlevelMass
        (I := I) (M := M) q cutoff u hu (fun _ => level)
          continuous_const a b
  have hmoving_int : IntervalIntegrable moving volume a b := by
    simpa only [moving] using
      intervalIntegrable_evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff.toFun u hu (fun _ => level)
          continuous_const hg cutoff.smooth a b
  have hpoint : ∀ t ∈ Icc a b, fixed t ≤ C.toReal * moving t := by
    intro t ht
    let μ := riemannianMeasureFamily (I := I) (M := M) g t
    let S : Set M := {x | level < u t x}
    let f : M → ℝ := fun x => cutoff.toFun x ^ 2
    letI : IsFiniteMeasure μ := by
      dsimp only [μ, riemannianMeasureFamily]
      exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
        (I := I) (M := M) (g t)
    letI : IsFiniteMeasure (C • μ) := μ.smul_finite hC
    have hf_int : Integrable f (C • μ) :=
      cutoff.smooth.continuous.pow 2 |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hmono := integral_mono_measure
      (Measure.restrict_mono_measure (hvolume t ht) S)
      (ae_of_all _ fun x => sq_nonneg (cutoff.toFun x)) hf_int.restrict
    rw [Measure.restrict_smul, integral_smul_measure] at hmono
    simpa only [fixed, moving, evolvingLocalizedSuperlevelMass, μ, S, f,
      smul_eq_mul] using hmono
  have hmono : (∫ t in a..b, fixed t) ≤
      ∫ t in a..b, C.toReal * moving t :=
    intervalIntegral.integral_mono_on hab hfixed_int
      (hmoving_int.const_mul C.toReal) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [localizedSpacetimeMeasure_real_superlevel cutoff hab
    (fun z => u z.1 z.2) hu.continuous]
  simpa only [fixed, moving] using hmono

omit [I.Boundaryless] in
theorem localizedSpacetimeMeasure_real_sublevel_le_evolvingLocalizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (cutoff : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b level t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        C • riemannianMeasureFamily (I := I) (M := M) g t) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | u z.1 z.2 < level} ≤
      C.toReal * ∫ t in a..b,
        evolvingLocalizedSublevelMass
          (I := I) (M := M) g cutoff.toFun u t level := by
  have h :=
    localizedSpacetimeMeasure_real_superlevel_le_evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g cutoff (fun t x => -u t x) hu.neg hab hg C hC
        hvolume (level := -level)
  simpa only [neg_lt_neg_iff, evolvingLocalizedSuperlevelMass,
    evolvingLocalizedSublevelMass] using h

omit [I.Boundaryless] in
theorem exists_localizedSpacetimeMeasure_real_superlevel_le_evolvingLocalizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (cutoff : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b level t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
          {z | level < u z.1 z.2} ≤
        C.toReal * ∫ t in a..b,
          evolvingLocalizedSuperlevelMass
            (I := I) (M := M) g cutoff.toFun u t level := by
  obtain ⟨C, hCzero, hCtop, hvolume⟩ := volume_uniform_equiv
    (I := I) (M := M) q g isCompact_Icc (fun x₀ i j =>
      (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc a b)) Set.Subset.rfl))
  refine ⟨C, hCzero, hCtop, ?_⟩
  exact localizedSpacetimeMeasure_real_superlevel_le_evolvingLocalizedSuperlevelMass
    (I := I) (M := M) g cutoff u hu hab hg C hCtop
      (fun t ht => (hvolume t ht).2)

omit [I.Boundaryless] in
theorem exists_localizedSpacetimeMeasure_real_sublevel_le_evolvingLocalizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (cutoff : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b level t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
          {z | u z.1 z.2 < level} ≤
        C.toReal * ∫ t in a..b,
          evolvingLocalizedSublevelMass
            (I := I) (M := M) g cutoff.toFun u t level := by
  obtain ⟨C, hCzero, hCtop, hvolume⟩ := volume_uniform_equiv
    (I := I) (M := M) q g isCompact_Icc (fun x₀ i j =>
      (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc a b)) Set.Subset.rfl))
  refine ⟨C, hCzero, hCtop, ?_⟩
  exact localizedSpacetimeMeasure_real_sublevel_le_evolvingLocalizedSublevelMass
    (I := I) (M := M) g cutoff u hu hab hg C hCtop
      (fun t ht => (hvolume t ht).2)

theorem early_localizedSpacetimeMeasure_centered_log_superlevel_tail_of_evolving_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (deviationCutoff : SmoothScalar q)
    (averagingCutoff : M → ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W Wdeviation : ℝ) {a τ t₀ r : ℝ}
    (haτ : a ≤ τ) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (Cvolume : ℝ≥0∞) (hCvolume : Cvolume ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a τ,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        Cvolume • riemannianMeasureFamily (I := I) (M := M) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc a τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff.toFun averagingCutoff Ctail (Icc a τ))
    (htrace : ∀ t ∈ Icc a τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc a τ,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdeviationMass_le : ∀ t ∈ Icc a τ,
      evolvingCutoffMass
        (I := I) (M := M) g deviationCutoff.toFun t ≤ Wdeviation)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ).real
        {z | evolvingLocalizedAverage
              (I := I) (M := M) g averagingCutoff
                (fun s x => Real.log (u s x)) τ + r <
            Real.log (u z.1 z.2)} ≤
      Cvolume.toReal *
        (max
            (2 * (∫ s in a..τ,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H s) *
              ((τ - a) * Wdeviation))
            (8 * Ctail * W) / r) := by
  have hlog := contMDiff_log_of_pos hu hpos
  have hbridge :=
    localizedSpacetimeMeasure_real_superlevel_le_evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g deviationCutoff
        (fun s x => Real.log (u s x)) hlog haτ hg Cvolume hCvolume hvolume
        (level := evolvingLocalizedAverage
          (I := I) (M := M) g averagingCutoff
            (fun s x => Real.log (u s x)) τ + r)
  have htail :=
    integrated_early_centered_evolving_log_superlevel_tail_of_supersolution
      (I := I) (M := M) g deviationCutoff.toFun averagingCutoff u hu hpos
        Ccenter Ctail H W Wdeviation haτ hr hCtail hg hgram
          deviationCutoff.smooth haveragingCutoff hne hPcenter hPtail htrace
            hmass_le hdeviationMass_le hpde
  exact hbridge.trans
    (mul_le_mul_of_nonneg_left htail ENNReal.toReal_nonneg)

theorem late_localizedSpacetimeMeasure_centered_log_sublevel_tail_of_evolving_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (deviationCutoff : SmoothScalar q)
    (averagingCutoff : M → ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W Wdeviation : ℝ) {τ b t₀ r : ℝ}
    (hτb : τ ≤ b) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (Cvolume : ℝ≥0∞) (hCvolume : Cvolume ≠ ⊤)
    (hvolume : ∀ t ∈ Icc τ b,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        Cvolume • riemannianMeasureFamily (I := I) (M := M) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ b))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff.toFun averagingCutoff Ctail (Icc τ b))
    (htrace : ∀ t ∈ Icc τ b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc τ b,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdeviationMass_le : ∀ t ∈ Icc τ b,
      evolvingCutoffMass
        (I := I) (M := M) g deviationCutoff.toFun t ≤ Wdeviation)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b).real
        {z | Real.log (u z.1 z.2) <
            evolvingLocalizedAverage
              (I := I) (M := M) g averagingCutoff
                (fun s x => Real.log (u s x)) τ - r} ≤
      Cvolume.toReal *
        (max
            (2 * (∫ s in τ..b,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H s) *
              ((b - τ) * Wdeviation))
            (8 * Ctail * W) / r) := by
  have hlog := contMDiff_log_of_pos hu hpos
  have hbridge :=
    localizedSpacetimeMeasure_real_sublevel_le_evolvingLocalizedSublevelMass
      (I := I) (M := M) g deviationCutoff
        (fun s x => Real.log (u s x)) hlog hτb hg Cvolume hCvolume hvolume
        (level := evolvingLocalizedAverage
          (I := I) (M := M) g averagingCutoff
            (fun s x => Real.log (u s x)) τ - r)
  have htail :=
    integrated_late_centered_evolving_log_sublevel_tail_of_supersolution
      (I := I) (M := M) g deviationCutoff.toFun averagingCutoff u hu hpos
        Ccenter Ctail H W Wdeviation hτb hr hCtail hg hgram
          deviationCutoff.smooth haveragingCutoff hne hPcenter hPtail htrace
            hmass_le hdeviationMass_le hpde
  exact hbridge.trans
    (mul_le_mul_of_nonneg_left htail ENNReal.toReal_nonneg)

theorem early_localizedSpacetimeMeasure_log_superlevel_tail_of_exponentialTimeRescale_of_evolving_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (deviationCutoff : SmoothScalar q)
    (averagingCutoff : M → ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W rate : ℝ) {a τ t₀ r : ℝ}
    (haτ : a ≤ τ) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (Cvolume : ℝ≥0∞) (hCvolume : Cvolume ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a τ,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        Cvolume • riemannianMeasureFamily (I := I) (M := M) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M ↦
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc a τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff.toFun averagingCutoff Ctail (Icc a τ))
    (htrace : ∀ t ∈ Icc a τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc a τ,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc a τ,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s ↦ u s x) t) :
    let center := evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff
        (fun s x ↦ Real.log (u s x)) τ + rate * τ
    (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ).real
        {z | r < Real.log (exponentialTimeRescale rate center u z.1 z.2)} ≤
      Cvolume.toReal * (4 * Ctail * W / r) := by
  let logu : ℝ → M → ℝ := fun s x ↦ Real.log (u s x)
  let center := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ + rate * τ
  let v := exponentialTimeRescale rate center u
  let logv : ℝ → M → ℝ := fun s x ↦ Real.log (v s x)
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hlogv := contMDiff_log_of_pos hv hvpos
  have hbridge :=
    localizedSpacetimeMeasure_real_superlevel_le_evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g deviationCutoff logv hlogv haτ hg
        Cvolume hCvolume hvolume (level := r)
  have htail :=
    integrated_early_evolving_log_superlevel_tail_of_exponentialTimeRescale_of_supersolution
      (I := I) (M := M) g deviationCutoff.toFun averagingCutoff u hu hpos
        Ccenter Ctail H W rate haτ hr hCtail hg hgram deviationCutoff.smooth
          haveragingCutoff hne hPcenter hPtail htrace hmass_le hdrift_le hpde
  exact hbridge.trans (by
    simpa only [logv, v, center, logu] using
      mul_le_mul_of_nonneg_left htail ENNReal.toReal_nonneg)

theorem late_localizedSpacetimeMeasure_log_sublevel_tail_of_exponentialTimeRescale_of_evolving_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (deviationCutoff : SmoothScalar q)
    (averagingCutoff : M → ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W rate : ℝ) {τ b t₀ r : ℝ}
    (hτb : τ ≤ b) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (Cvolume : ℝ≥0∞) (hCvolume : Cvolume ≠ ⊤)
    (hvolume : ∀ t ∈ Icc τ b,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        Cvolume • riemannianMeasureFamily (I := I) (M := M) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M ↦
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ b))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff.toFun averagingCutoff Ctail (Icc τ b))
    (htrace : ∀ t ∈ Icc τ b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc τ b,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc τ b,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s ↦ u s x) t) :
    let center := evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff
        (fun s x ↦ Real.log (u s x)) τ + rate * τ
    (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b).real
        {z | Real.log (exponentialTimeRescale rate center u z.1 z.2) < -r} ≤
      Cvolume.toReal * (4 * Ctail * W / r) := by
  let logu : ℝ → M → ℝ := fun s x ↦ Real.log (u s x)
  let center := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ + rate * τ
  let v := exponentialTimeRescale rate center u
  let logv : ℝ → M → ℝ := fun s x ↦ Real.log (v s x)
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hlogv := contMDiff_log_of_pos hv hvpos
  have hbridge :=
    localizedSpacetimeMeasure_real_sublevel_le_evolvingLocalizedSublevelMass
      (I := I) (M := M) g deviationCutoff logv hlogv hτb hg
        Cvolume hCvolume hvolume (level := -r)
  have htail :=
    integrated_late_evolving_log_sublevel_tail_of_exponentialTimeRescale_of_supersolution
      (I := I) (M := M) g deviationCutoff.toFun averagingCutoff u hu hpos
        Ccenter Ctail H W rate hτb hr hCtail hg hgram deviationCutoff.smooth
          haveragingCutoff hne hPcenter hPtail htrace hmass_le hdrift_le hpde
  exact hbridge.trans (by
    simpa only [logv, v, center, logu] using
      mul_le_mul_of_nonneg_left htail ENNReal.toReal_nonneg)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
