import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingSobolev
import DifferentialGeometry.Analysis.Parabolic.Moser.Power

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedL2Mass_rpow_half
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hpos : ∀ t x, 0 < u t x) (p t : ℝ) :
    evolvingLocalizedL2Mass
        (I := I) (M := M) g cutoff (fun s x => u s x ^ (p / 2)) t =
      evolvingLocalizedIntegral
        (I := I) (M := M) g cutoff (fun s x => u s x ^ p) t := by
  unfold evolvingLocalizedL2Mass evolvingLocalizedIntegral
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  rw [← Real.rpow_natCast (u t x ^ (p / 2)) 2,
    ← Real.rpow_mul (hpos t x).le]
  congr 1
  ring

theorem caccioppoli_evolving_positive_rpow_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    (t B : ℝ) (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (htrace : ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hpde : ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (2 * (1 - q) / q) *
        evolvingLocalizedDirichletEnergy
          (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2)) t ≤
      deriv
          (evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2))) t +
        (2 * q / (1 - q)) *
          evolvingCutoffGradientError
            (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2)) t +
        (1 / 2) * B *
          evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2)) t := by
  let huHalf := contMDiff_rpow_of_pos hu hpos (q / 2)
  let huq := contMDiff_rpow_of_pos hu hpos q
  let w : ℝ → M → ℝ := fun s x => u s x ^ (q / 2)
  let uq : ℝ → M → ℝ := fun s x => u s x ^ q
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff w
  let timeIntegral : ℝ :=
    ∫ x, cutoff x ^ 2 * deriv (fun s => uq s x) t
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  have hfixed := caccioppoli_positive_rpow_of_supersolution
    (I := I) (M := M) (g t) cutoff_t u hu hpos hq_pos hq_one t hpde
  have hfixedDeriv := hasDerivAt_localizedIntegral
    (I := I) (M := M) cutoff_t uq huq t
  rw [hfixedDeriv.deriv] at hfixed
  have hfixed' :
      (2 * (1 - q) / q) *
          evolvingLocalizedDirichletEnergy
            (I := I) (M := M) g cutoff w t ≤
        timeIntegral + (2 * q / (1 - q)) *
          evolvingCutoffGradientError
            (I := I) (M := M) g cutoff w t := by
    simpa only [w, uq, huHalf, cutoff_t, timeIntegral,
      evolvingLocalizedDirichletEnergy, localizedDirichletEnergy,
      evolvingCutoffGradientError, cutoffGradientError,
      riemannianMeasureFamily_def] using hfixed
  have hmass_eq : mass =
      evolvingLocalizedIntegral (I := I) (M := M) g cutoff uq := by
    funext s
    simpa only [mass, w, uq] using
      evolvingLocalizedL2Mass_rpow_half
        (I := I) (M := M) g cutoff u hpos q s
  have hmoving := hasDerivAt_evolvingLocalizedIntegral
    (I := I) (M := M) g cutoff uq t hg hcutoff huq
  have huq_t : Continuous (uq t) :=
    (huq.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => uq p.1 p.2, huq⟩
  have htime : Continuous (fun x : M => deriv (fun s => uq s x) t) := by
    exact ((DifferentialGeometry.contMDiff_partial_deriv_fst I F).comp
      (contMDiff_const.prodMk contMDiff_id)).continuous
  have htrace_cont : Continuous
      (fun x : M => traceTimeDerivMetric (I := I) g t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hg
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have htime_int : Integrable
      (fun x : M => cutoff x ^ 2 * deriv (fun s => uq s x) t) μ :=
    ((hcutoff.continuous.pow 2).mul htime).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdist_int : Integrable (fun x : M => cutoff x ^ 2 *
      ((1 / 2) * traceTimeDerivMetric (I := I) g t x * uq t x)) μ :=
    ((hcutoff.continuous.pow 2).mul
      ((continuous_const.mul htrace_cont).mul huq_t))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hderiv_split : deriv mass t = timeIntegral +
      evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff w t := by
    rw [hmass_eq, hmoving.deriv]
    change (∫ x, cutoff x ^ 2 *
        (deriv (fun s => uq s x) t +
          (1 / 2) * traceTimeDerivMetric (I := I) g t x * uq t x) ∂μ) =
      (∫ x, cutoff x ^ 2 * deriv (fun s => uq s x) t ∂μ) +
        ∫ x, cutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x * w t x ^ 2) ∂μ
    have hdist_eq :
        (∫ x, cutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x * w t x ^ 2) ∂μ) =
          ∫ x, cutoff x ^ 2 *
            ((1 / 2) * traceTimeDerivMetric (I := I) g t x * uq t x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      have hrpow : w t x ^ 2 = uq t x := by
        dsimp only [w, uq]
        rw [← Real.rpow_natCast (u t x ^ (q / 2)) 2,
          ← Real.rpow_mul (hpos t x).le]
        congr 1
        ring
      rw [hrpow]
    rw [hdist_eq, ← integral_add htime_int hdist_int]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hdist := neg_evolvingLocalizedVolumeDistortion_le
    (I := I) (M := M) g cutoff w t B hg hcutoff.continuous
      ((huHalf.comp (contMDiff_const.prodMk contMDiff_id)).continuous) htrace
  have htime_le : timeIntegral ≤ deriv mass t + (1 / 2) * B * mass t := by
    rw [hderiv_split]
    linarith
  have hcombined :
      timeIntegral + (2 * q / (1 - q)) *
          evolvingCutoffGradientError
            (I := I) (M := M) g cutoff w t ≤
        deriv mass t + (2 * q / (1 - q)) *
            evolvingCutoffGradientError
              (I := I) (M := M) g cutoff w t +
          (1 / 2) * B * mass t := by
    calc
      _ ≤ (deriv mass t + (1 / 2) * B * mass t) +
          (2 * q / (1 - q)) *
            evolvingCutoffGradientError
              (I := I) (M := M) g cutoff w t :=
        add_le_add htime_le le_rfl
      _ = _ := by ring
  have hresult := hfixed'.trans hcombined
  simpa only [mass, w] using hresult

theorem weighted_caccioppoli_evolving_positive_rpow_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    {t₀ : ℝ} (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    {weight dweight : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (htrace : ∀ t ∈ Icc a b, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    weight a * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2)) a -
        weight b * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2)) b +
        ∫ t in a..b, weight t *
          ((2 * (1 - q) / q) *
            evolvingLocalizedDirichletEnergy
              (I := I) (M := M) g cutoff
                (fun s x => u s x ^ (q / 2)) t) ≤
      ∫ t in a..b,
        (-dweight t) * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2)) t +
          weight t *
            ((2 * q / (1 - q)) *
                evolvingCutoffGradientError
                  (I := I) (M := M) g cutoff
                    (fun s x => u s x ^ (q / 2)) t +
              (1 / 2) * B * evolvingLocalizedL2Mass
                (I := I) (M := M) g cutoff
                  (fun s x => u s x ^ (q / 2)) t) := by
  let huHalf := contMDiff_rpow_of_pos hu hpos (q / 2)
  let w : ℝ → M → ℝ := fun t x => u t x ^ (q / 2)
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff w
  let dirichlet : ℝ → ℝ :=
    evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff w
  let error : ℝ → ℝ :=
    evolvingCutoffGradientError (I := I) (M := M) g cutoff w
  let c := 2 * (1 - q) / q
  let e := 2 * q / (1 - q)
  let v := (1 / 2) * B
  let negMass : ℝ → ℝ := fun t => -mass t
  have hmass_cont : ContinuousOn mass (Icc a b) := by
    simpa only [mass] using evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g cutoff w isCompact_Icc hg
        hcutoff.continuous huHalf.continuous
  have hdmass_cont : ContinuousOn (deriv mass) (Icc a b) := by
    simpa only [mass] using deriv_evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g cutoff w isCompact_Icc hg hcutoff huHalf
  have hmass_deriv : ∀ t ∈ Icc a b,
      HasDerivAt mass (deriv mass t) t := by
    intro t _
    have hraw := hasDerivAt_evolvingLocalizedL2Mass
      (I := I) (M := M) g cutoff w t (hg.at_any t) hcutoff huHalf
    simpa only [mass] using hraw.congr_deriv hraw.deriv.symm
  have hnegMass_deriv : ∀ t ∈ Icc a b,
      HasDerivAt negMass (deriv negMass t) t := by
    intro t ht
    exact (hmass_deriv t ht).neg.congr_deriv
      ((hmass_deriv t ht).neg.deriv.symm)
  have hdnegMass_cont : ContinuousOn (deriv negMass) (Icc a b) := by
    have heq : deriv negMass = fun t => -deriv mass t := by
      funext t
      have hraw := hasDerivAt_evolvingLocalizedL2Mass
        (I := I) (M := M) g cutoff w t (hg.at_any t) hcutoff huHalf
      have hmass_at : HasDerivAt mass (deriv mass t) t := by
        simpa only [mass] using hraw.congr_deriv hraw.deriv.symm
      simpa only [negMass] using hmass_at.neg.deriv
    rw [heq]
    exact hdmass_cont.neg
  have hdirichlet : ContinuousOn dirichlet (Icc a b) := by
    simpa only [dirichlet] using evolvingLocalizedDirichletEnergy_continuousOn
      (I := I) (M := M) g cutoff w isCompact_Icc hg hgram hcutoff huHalf
  have herror : ContinuousOn error (Icc a b) := by
    simpa only [error] using evolvingCutoffGradientError_continuousOn
      (I := I) (M := M) g cutoff w isCompact_Icc hg hgram hcutoff huHalf
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hdissipation : ContinuousOn
      (fun t => weight t * (c * dirichlet t)) (Icc a b) :=
    hweight_cont.mul (continuousOn_const.mul hdirichlet)
  have hrhs : ContinuousOn
      (fun t => dweight t * negMass t +
        weight t * (e * error t + v * mass t)) (Icc a b) :=
    (hdweight.mul hmass_cont.neg).add
      (hweight_cont.mul
        ((continuousOn_const.mul herror).add
          (continuousOn_const.mul hmass_cont)))
  have hpointwise : ∀ t ∈ Icc a b,
      dweight t * negMass t + weight t * deriv negMass t +
          weight t * (c * dirichlet t) ≤
        dweight t * negMass t + weight t * (e * error t + v * mass t) := by
    intro t ht
    have hdiff := caccioppoli_evolving_positive_rpow_of_supersolution
      (I := I) (M := M) g cutoff u hu hpos hq_pos hq_one t B
        (hg.at_any t) hcutoff (htrace t ht) (hpde t ht)
    have hneg_deriv : deriv negMass t = -deriv mass t := by
      simpa only [negMass] using (hmass_deriv t ht).neg.deriv
    have hbase : deriv negMass t + c * dirichlet t ≤
        e * error t + v * mass t := by
      rw [hneg_deriv]
      simpa only [c, e, v, dirichlet, error, mass, w] using (show
        -deriv mass t +
            (2 * (1 - q) / q) * dirichlet t ≤
          (2 * q / (1 - q)) * error t + (1 / 2) * B * mass t by
        linarith)
    have hmul := mul_le_mul_of_nonneg_left hbase (hweight_nonneg t ht)
    ring_nf at hmul ⊢
    linarith
  have hresult := weight_mul_energy_inequality
    hab hdweight hweight hdnegMass_cont hnegMass_deriv hdissipation hrhs hpointwise
  simp only [negMass, mass, dirichlet, error, c, e, v, w,
    mul_neg, sub_neg_eq_add] at hresult
  convert hresult using 1
  · ring
  · apply intervalIntegral.integral_congr
    intro t _
    ring

theorem backward_caccioppoli_evolving_inner_energy_positive_rpow_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    {t₀ : ℝ} (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    {weight dweight : ℝ → ℝ} {a t₁ b A B : ℝ}
    (hat₁ : a ≤ t₁) (ht₁b : t₁ ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hweight_b : weight b = 0)
    (hweight_inner : ∀ t ∈ Icc a t₁, weight t = 1)
    (htrace : ∀ t ∈ Icc a b, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hrhs_le : ∀ t ∈ Icc a t₁,
      (∫ s in t..b,
        (-dweight s) * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun r x => u r x ^ (q / 2)) s +
          weight s *
            ((2 * q / (1 - q)) *
                evolvingCutoffGradientError
                  (I := I) (M := M) g cutoff
                    (fun r x => u r x ^ (q / 2)) s +
              (1 / 2) * B * evolvingLocalizedL2Mass
                (I := I) (M := M) g cutoff
                  (fun r x => u r x ^ (q / 2)) s)) ≤ A) :
    (∀ t ∈ Icc a t₁,
      evolvingLocalizedL2Mass
        (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2)) t ≤ A) ∧
      (∫ t in a..t₁,
        evolvingLocalizedDirichletEnergy
          (I := I) (M := M) g cutoff (fun s x => u s x ^ (q / 2)) t) ≤
        (q / (2 * (1 - q))) * A := by
  let huHalf := contMDiff_rpow_of_pos hu hpos (q / 2)
  let w : ℝ → M → ℝ := fun t x => u t x ^ (q / 2)
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff w
  let dirichlet : ℝ → ℝ :=
    evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff w
  let error : ℝ → ℝ :=
    evolvingCutoffGradientError (I := I) (M := M) g cutoff w
  let c := 2 * (1 - q) / q
  let e := 2 * q / (1 - q)
  let v := (1 / 2) * B
  let dissipation : ℝ → ℝ := fun t => c * dirichlet t
  let source : ℝ → ℝ := fun t =>
    (-dweight t) * mass t + weight t * (e * error t + v * mass t)
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hdirichlet_cont : ContinuousOn dirichlet (Icc a b) := by
    simpa only [dirichlet] using evolvingLocalizedDirichletEnergy_continuousOn
      (I := I) (M := M) g cutoff w isCompact_Icc hg hgram hcutoff huHalf
  have hdissipation_cont : ContinuousOn dissipation (Icc a b) :=
    continuousOn_const.mul hdirichlet_cont
  have hc_pos : 0 < c := by
    dsimp only [c]
    exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hq_one)) hq_pos
  have hbase := backward_inner_mass_and_dissipation_le
    (weight := weight) (mass := mass) (dissipation := dissipation) (source := source)
    hat₁ ht₁b hweight_cont hdissipation_cont hweight_nonneg
    (fun t _ => mul_nonneg hc_pos.le
      (evolvingLocalizedDirichletEnergy_nonneg
        (I := I) (M := M) g cutoff w t))
    hweight_b hweight_inner
    (fun t _ => evolvingLocalizedL2Mass_nonneg
      (I := I) (M := M) g cutoff w t)
    (by simpa only [source, mass, error, e, v, w] using hrhs_le)
    (fun t ht => by
      have htb : t ≤ b := ht.2.trans ht₁b
      have hsubset : Icc t b ⊆ Icc a b :=
        fun s hs => ⟨ht.1.trans hs.1, hs.2⟩
      have henergy := weighted_caccioppoli_evolving_positive_rpow_of_supersolution
        (I := I) (M := M) g cutoff u hu hpos hq_pos hq_one hg hgram hcutoff
          htb (hdweight.mono hsubset)
            (fun s hs => hweight s (hsubset hs))
              (fun s hs => hweight_nonneg s (hsubset hs))
                (fun s hs => htrace s (hsubset hs))
                  (fun s hs => hpde s (hsubset hs))
      simpa only [mass, dirichlet, error, dissipation, source, c, e, v, w]
        using henergy)
  refine ⟨by simpa only [mass, w] using hbase.1, ?_⟩
  have hscaled : c * (∫ t in a..t₁, dirichlet t) ≤ A := by
    rw [← intervalIntegral.integral_const_mul]
    simpa only [dissipation] using hbase.2
  let k := q / (2 * (1 - q))
  have hk_nonneg : 0 ≤ k := by
    dsimp only [k]
    exact div_nonneg hq_pos.le
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hq_one.le))
  have hkc : k * c = 1 := by
    dsimp only [k, c]
    field_simp [hq_pos.ne', sub_ne_zero.mpr (ne_of_gt hq_one)]
  have hmul := mul_le_mul_of_nonneg_left hscaled hk_nonneg
  rw [← mul_assoc, hkc, one_mul] at hmul
  simpa only [dirichlet, k, w] using hmul

theorem caccioppoli_evolving_rpow_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {t₀ : ℝ} (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x + source t x) :
    weight b * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff (fun s x => u s x ^ q) b -
        weight a * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff (fun s x => u s x ^ q) a +
        ∫ t in a..b, weight t *
          evolvingLocalizedDirichletEnergy
            (I := I) (M := M) g cutoff (fun s x => u s x ^ q) t ≤
      ∫ t in a..b,
        dweight t * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun s x => u s x ^ q) t +
          weight t *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff (fun s x => u s x ^ q) t +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff (fun s x => u s x ^ q)
                  (rpowSource q u source) t +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff (fun s x => u s x ^ q) t) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let hsourceq := contMDiff_rpowSource_of_pos hu hsource hpos q
  apply caccioppoli_evolving_of_subsolution
    (I := I) (M := M) g cutoff (fun t x => u t x ^ q)
      (rpowSource q u source) hcutoff huq hsourceq hg hgram hab hdweight
      hweight hweight_nonneg
  · intro t _ x
    exact (Real.rpow_pos_of_pos (hpos t x) q).le
  · intro t ht x
    exact rpow_subsolution
      (I := I) (M := M) (g t) u source hu hpos hq (hpde t ht x)

theorem evolving_rpow_moser_step_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (houter : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ outer)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {t : ℝ} (hg : MetricFamilyRegularAt (I := I) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {C : ℝ} (hC : 0 ≤ C)
    {weight dweight : ℝ → ℝ} {a t₀ t₁ A K L : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hdweight : ContinuousOn dweight (Icc a t₁))
    (hweight : ∀ t ∈ Icc a t₁, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a t₁, 0 ≤ weight t)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ t ∈ Icc t₀ t₁, weight t = 1)
    (hSobolev : ∀ t ∈ Icc t₀ t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x + source t x)
    (hrhs_le : ∀ t ∈ Icc t₀ t₁,
      (∫ s in a..t,
        dweight s * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun r x => u r x ^ q) s +
          weight s *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff (fun r x => u r x ^ q) s +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff (fun r x => u r x ^ q)
                  (rpowSource q u source) s +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff (fun r x => u r x ^ q) s)) ≤ A)
    (hgrad : ∀ t ∈ Icc t₀ t₁, ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t) cutoff x)
          (gradientFun (I := I) (g t) cutoff x) ≤
        K * outer x ^ 2)
    (houterMass_le :
      (∫ t in t₀..t₁,
        evolvingLocalizedL2Mass
          (I := I) (M := M) g outer (fun s x => u s x ^ q) t) ≤ L) :
    (∫ t in t₀..t₁, ∫ x,
        |cutoff x * u t x ^ q| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) ≤
      C * (((t₁ - t₀ + 1) * A + K * L) ^
        (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let sourceq := rpowSource q u source
  have hsourceq : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => sourceq p.1 p.2) := by
    simpa only [sourceq] using contMDiff_rpowSource_of_pos hu hsource hpos q
  have hpdeq : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x ^ q) t ≤
        Δ_g (I := I) (g t)
            (smoothScalarSlice (I := I) (g t)
              (fun s x => u s x ^ q) huq t).toContMDiffMap x +
          sourceq t x := by
    intro t ht x
    simpa only [huq, sourceq] using rpow_subsolution
      (I := I) (M := M) (g t) u source hu hpos hq (hpde t ht x)
  have henergy := caccioppoli_evolving_inner_energy_of_subsolution
    (I := I) (M := M) g cutoff (fun t x => u t x ^ q) sourceq
      hcutoff huq hsourceq hg hgram hat₀ ht₀t₁ hdweight hweight
      hweight_nonneg hweight_a hweight_inner
      (fun t _ x => (Real.rpow_pos_of_pos (hpos t x) q).le) hpdeq
      (by simpa only [huq, sourceq] using hrhs_le)
  apply evolving_localized_parabolic_sobolev_of_nested_cutoffs_le
    (I := I) (M := M) g hdim cutoff outer hcutoff houter
      (fun t x => u t x ^ q) huq ht₀t₁ hA hC hK hg hgram hSobolev
      henergy.1 henergy.2 hgrad
  simpa only [huq] using houterMass_le

theorem evolving_rpow_moser_step_homogeneous_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (houter : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ outer)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {t : ℝ} (hg : MetricFamilyRegularAt (I := I) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {C a t₀ t₁ B D K L : ℝ} (hC : 0 ≤ C)
    (hSobolev : ∀ s ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g s) hdim ≤ C)
    (hat₀ : a < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hpde : ∀ s ∈ Icc a t₁, ∀ x : M,
      deriv (fun r => u r x) s ≤
        Δ_g (I := I) (g s)
          (smoothScalarSlice (I := I) (g s) u hu s).toContMDiffMap x)
    (hcutoff_le : ∀ x : M, cutoff x ^ 2 ≤ outer x ^ 2)
    (hgrad : ∀ s ∈ Icc a t₁, ∀ x : M,
      (g s).inner x
          (gradientFun (I := I) (g s) cutoff x)
          (gradientFun (I := I) (g s) cutoff x) ≤
        K * outer x ^ 2)
    (hderiv_le : ∀ s ∈ Icc a t₁, timeCutoffDeriv a t₀ s ≤ D)
    (htrace : ∀ s ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g s x ≤ B)
    (houterMass_le :
      (∫ s in a..t₁,
        evolvingLocalizedL2Mass
          (I := I) (M := M) g outer (fun r x => u r x ^ q) s) ≤ L) :
    (∫ s in t₀..t₁, ∫ x,
        |cutoff x * u s x ^ q| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g s)) ≤
      C * (((t₁ - t₀ + 1) *
          ((D + 4 * K + (1 / 2) * B) * L) + K * L) ^
        (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let zeroSource : ℝ → M → ℝ := fun _ _ => 0
  have hzeroSource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => zeroSource p.1 p.2) := contMDiff_const
  have hrhs_le : ∀ s ∈ Icc t₀ t₁,
      (∫ r in a..s,
        timeCutoffDeriv a t₀ r * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun z x => u z x ^ q) r +
          timeCutoff a t₀ r *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff (fun z x => u z x ^ q) r +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff (fun z x => u z x ^ q)
                  (rpowSource q u zeroSource) r +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff (fun z x => u z x ^ q) r)) ≤
        (D + 4 * K + (1 / 2) * B) * L := by
    intro s hs
    have hraw := timeCutoff_caccioppoli_evolving_rhs_le
      (I := I) (M := M) g cutoff outer hcutoff houter
        (fun r x => u r x ^ q) huq hat₀ hs.1 hs.2 hB hD hK hg hgram
        hcutoff_le hgrad hderiv_le htrace
        (by simpa only [huq] using houterMass_le)
    simpa only [zeroSource, rpowSource, mul_zero, evolvingLocalizedForcing,
      integral_zero, add_zero, huq] using hraw
  have houterMass_inner_le :
      (∫ s in t₀..t₁,
        evolvingLocalizedL2Mass
          (I := I) (M := M) g outer (fun r x => u r x ^ q) s) ≤ L := by
    let mass : ℝ → ℝ := fun s =>
      evolvingLocalizedL2Mass
        (I := I) (M := M) g outer (fun r x => u r x ^ q) s
    have hmass_cont : ContinuousOn mass (Icc a t₁) := by
      simpa only [mass] using evolvingLocalizedL2Mass_continuousOn
        (I := I) (M := M) g outer (fun r x => u r x ^ q)
          isCompact_Icc hg houter.continuous huq.continuous
    have hmass_int : IntervalIntegrable mass volume a t₁ := by
      apply ContinuousOn.intervalIntegrable
      simpa [uIcc_of_le (hat₀.le.trans ht₀t₁)] using hmass_cont
    have hmono : (∫ s in t₀..t₁, mass s) ≤ ∫ s in a..t₁, mass s :=
      intervalIntegral.integral_mono_interval hat₀.le ht₀t₁ le_rfl
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact evolvingLocalizedL2Mass_nonneg
            (I := I) (M := M) g outer (fun r x => u r x ^ q) s)
        hmass_int
    exact hmono.trans (by simpa only [mass, huq] using houterMass_le)
  apply evolving_rpow_moser_step_le
    (I := I) (M := M) g hdim cutoff outer hcutoff houter u zeroSource
      hu hzeroSource hpos hq hg hgram hC hat₀.le ht₀t₁
      (mul_nonneg
        (add_nonneg (add_nonneg hD (mul_nonneg (by norm_num) hK))
          (mul_nonneg (by norm_num) hB)) hL)
      hK (contDiff_timeCutoffDeriv a t₀).continuous.continuousOn
      (fun s _ => hasDerivAt_timeCutoff a t₀ s)
      (fun s _ => (timeCutoff_mem_Icc a t₀ s).1)
      (timeCutoff_eq_zero a hat₀)
      (fun s hs => timeCutoff_eq_one_of_le hat₀ hs.1)
      (fun s hs => hSobolev s ⟨hat₀.le.trans hs.1, hs.2⟩)
  · intro s hs x
    simpa only [zeroSource, add_zero] using hpde s hs x
  · simpa only [huq, zeroSource] using hrhs_le
  · intro s hs
    exact hgrad s ⟨hat₀.le.trans hs.1, hs.2⟩
  · simpa only [huq] using houterMass_inner_le

end DifferentialGeometry.Analysis.Parabolic.Moser

end
