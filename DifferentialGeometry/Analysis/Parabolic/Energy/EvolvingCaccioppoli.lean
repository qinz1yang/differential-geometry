import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Analysis.Parabolic.Energy.EvolvingMass

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Energy

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def evolvingLocalizedDirichletEnergy
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, cutoff x ^ 2 *
      (g t).inner x
        (gradientFun (I := I) (g t) (u t) x)
        (gradientFun (I := I) (g t) (u t) x)
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingCutoffGradientError
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, u t x ^ 2 *
      (g t).inner x
        (gradientFun (I := I) (g t) cutoff x)
        (gradientFun (I := I) (g t) cutoff x)
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingLocalizedForcing
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedDirichletEnergy_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) :
    0 ≤ evolvingLocalizedDirichletEnergy
      (I := I) (M := M) g cutoff u t := by
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
    (metric_inner_self_nonneg (I := I) (M := M) (g t) x _)

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingCutoffGradientError_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) :
    0 ≤ evolvingCutoffGradientError (I := I) (M := M) g cutoff u t := by
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
    (metric_inner_self_nonneg (I := I) (M := M) (g t) x _)

omit [I.Boundaryless] in
theorem evolvingLocalizedL2Mass_le_of_sq_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (cutoff outer : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (houter : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ outer)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ)
    (hle : ∀ x : M, cutoff x ^ 2 ≤ outer x ^ 2) :
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t ≤
      evolvingLocalizedL2Mass (I := I) (M := M) g outer u t := by
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let outer_t : SmoothScalar (g t) := ⟨outer, houter⟩
  let u_t : SmoothScalar (g t) :=
    ⟨u t, hu.comp (contMDiff_const.prodMk contMDiff_id)⟩
  have hfixed := localizedL2Mass_le_of_sq_le
    (I := I) (M := M) cutoff_t outer_t u_t hle
  simpa only [evolvingLocalizedL2Mass, localizedL2Mass,
    riemannianMeasureFamily_def, cutoff_t, outer_t, u_t] using hfixed

theorem evolvingCutoffGradientError_le_evolvingLocalizedL2Mass
    (g : ℝ → SmoothRiemannianMetric I M)
    (cutoff outer : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (houter : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ outer)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) {K : ℝ}
    (hgrad : ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t) cutoff x)
          (gradientFun (I := I) (g t) cutoff x) ≤
        K * outer x ^ 2) :
    evolvingCutoffGradientError (I := I) (M := M) g cutoff u t ≤
      K * evolvingLocalizedL2Mass (I := I) (M := M) g outer u t := by
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let outer_t : SmoothScalar (g t) := ⟨outer, houter⟩
  let u_t : SmoothScalar (g t) :=
    ⟨u t, hu.comp (contMDiff_const.prodMk contMDiff_id)⟩
  have hfixed := cutoffGradientError_le_localizedL2Mass
    (I := I) (M := M) cutoff_t outer_t u_t hgrad
  simpa only [evolvingCutoffGradientError, evolvingLocalizedL2Mass,
    cutoffGradientError, localizedL2Mass, riemannianMeasureFamily_def,
    cutoff_t, outer_t, u_t] using hfixed

omit [I.Boundaryless] in
theorem evolvingLocalizedDirichletEnergy_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContinuousOn
      (evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u) K := by
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    { metric := g
      connection := fun s => LeviCivita (I := I) (g s)
      metricCompatible := fun s => by
        simpa [LeviCivita] using
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (g s)) }
  have hgrad : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M =>
        (g p.1).inner p.2
          (gradientFun (I := I) (g p.1) (u p.1) p.2)
          (gradientFun (I := I) (g p.1) (u p.1) p.2)) := by
    have hraw := gradSq_joint (I := I) G.metric isOpen_univ hgram u hu.contMDiffOn
    simpa only [G, Set.univ_prod_univ, contMDiffOn_univ] using hraw
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact (((hcutoff.continuous.comp continuous_snd).pow 2).mul
      hgrad.continuous).continuousOn

omit [I.Boundaryless] in
theorem evolvingCutoffGradientError_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContinuousOn
      (evolvingCutoffGradientError (I := I) (M := M) g cutoff u) K := by
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    { metric := g
      connection := fun s => LeviCivita (I := I) (g s)
      metricCompatible := fun s => by
        simpa [LeviCivita] using
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (g s)) }
  have hcutoff_joint : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => cutoff p.2) :=
    hcutoff.comp contMDiff_snd
  have hgrad : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M =>
        (g p.1).inner p.2
          (gradientFun (I := I) (g p.1) cutoff p.2)
          (gradientFun (I := I) (g p.1) cutoff p.2)) := by
    have hraw := gradSq_joint (I := I) G.metric isOpen_univ hgram
      (fun _ => cutoff) hcutoff_joint.contMDiffOn
    simpa only [G, Set.univ_prod_univ, contMDiffOn_univ] using hraw
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact ((hu.continuous.pow 2).mul hgrad.continuous).continuousOn

omit [I.Boundaryless] in
theorem evolvingCutoffGradientError_continuous
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    Continuous (evolvingCutoffGradientError
      (I := I) (M := M) g cutoff u) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hlocal := evolvingCutoffGradientError_continuousOn
    (I := I) (M := M) g cutoff u
      (K := Icc (t - 1) (t + 1)) isCompact_Icc hg hgram hcutoff hu
  exact hlocal.continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

theorem intervalIntegral_evolvingCutoffGradientError_le_evolvingLocalizedL2Mass
    (g : ℝ → SmoothRiemannianMetric I M)
    (cutoff outer : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (houter : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ outer)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b K t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgrad : ∀ t ∈ Icc a b, ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t) cutoff x)
          (gradientFun (I := I) (g t) cutoff x) ≤
        K * outer x ^ 2) :
    (∫ t in a..b,
      evolvingCutoffGradientError (I := I) (M := M) g cutoff u t) ≤
      K * ∫ t in a..b,
        evolvingLocalizedL2Mass (I := I) (M := M) g outer u t := by
  let error : ℝ → ℝ := fun t =>
    evolvingCutoffGradientError (I := I) (M := M) g cutoff u t
  let outerMass : ℝ → ℝ := fun t =>
    evolvingLocalizedL2Mass (I := I) (M := M) g outer u t
  have herror_cont : ContinuousOn error (Icc a b) := by
    simpa only [error] using evolvingCutoffGradientError_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  have hmass_cont : ContinuousOn outerMass (Icc a b) := by
    simpa only [outerMass] using evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g outer u isCompact_Icc hg
        houter.continuous hu.continuous
  have herror_int : IntervalIntegrable error volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using herror_cont
  have hmass_int : IntervalIntegrable outerMass volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hmass_cont
  have hmono : (∫ t in a..b, error t) ≤ ∫ t in a..b, K * outerMass t :=
    intervalIntegral.integral_mono_on hab herror_int (hmass_int.const_mul K)
      (fun t ht => evolvingCutoffGradientError_le_evolvingLocalizedL2Mass
        (I := I) (M := M) g cutoff outer hcutoff houter u hu t
          (hgrad t ht))
  rw [intervalIntegral.integral_const_mul] at hmono
  simpa only [error, outerMass] using hmono

theorem timeCutoff_caccioppoli_evolving_rhs_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (cutoff outer : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (houter : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ outer)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a t₀ t t₁ B D K L s₀ : ℝ}
    (hat₀ : a < t₀) (ht₀t : t₀ ≤ t) (htt₁ : t ≤ t₁)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
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
        evolvingLocalizedL2Mass (I := I) (M := M) g outer u s) ≤ L) :
    (∫ s in a..t,
      timeCutoffDeriv a t₀ s *
          evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u s +
        timeCutoff a t₀ s *
          (4 * evolvingCutoffGradientError
              (I := I) (M := M) g cutoff u s +
            evolvingLocalizedVolumeDistortion
              (I := I) (M := M) g cutoff u s)) ≤
      (D + 4 * K + (1 / 2) * B) * L := by
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u
  let error : ℝ → ℝ :=
    evolvingCutoffGradientError (I := I) (M := M) g cutoff u
  let distortion : ℝ → ℝ :=
    evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u
  let outerMass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g outer u
  let lhs : ℝ → ℝ := fun s =>
    timeCutoffDeriv a t₀ s * mass s +
      timeCutoff a t₀ s * (4 * error s + distortion s)
  let coefficient : ℝ := D + 4 * K + (1 / 2) * B
  have hat : a ≤ t := hat₀.le.trans ht₀t
  have hat₁ : a ≤ t₁ := hat.trans htt₁
  have hmass_cont : ContinuousOn mass (Icc a t₁) := by
    simpa only [mass] using evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg
        hcutoff.continuous hu.continuous
  have herror_cont : ContinuousOn error (Icc a t₁) := by
    simpa only [error] using evolvingCutoffGradientError_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  have hdistortion_cont : ContinuousOn distortion (Icc a t₁) := by
    simpa only [distortion] using evolvingLocalizedVolumeDistortion_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg
        hcutoff.continuous hu.continuous
  have houter_cont : ContinuousOn outerMass (Icc a t₁) := by
    simpa only [outerMass] using evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g outer u isCompact_Icc hg
        houter.continuous hu.continuous
  have hlhs_cont : ContinuousOn lhs (Icc a t) := by
    have hsubset : Icc a t ⊆ Icc a t₁ := fun s hs =>
      ⟨hs.1, hs.2.trans htt₁⟩
    exact ((contDiff_timeCutoffDeriv a t₀).continuous.continuousOn.mul
      (hmass_cont.mono hsubset)).add
        ((contDiff_timeCutoff a t₀).continuous.continuousOn.mul
          ((continuousOn_const.mul (herror_cont.mono hsubset)).add
            (hdistortion_cont.mono hsubset)))
  have houter_int : IntervalIntegrable outerMass volume a t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hat₁] using houter_cont
  have hlhs_int : IntervalIntegrable lhs volume a t := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hat] using hlhs_cont
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have hrhs_int : IntervalIntegrable (fun s => coefficient * outerMass s)
      volume a t := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hat] using continuousOn_const.mul
      (houter_cont.mono (fun s hs => ⟨hs.1, hs.2.trans htt₁⟩))
  have hpoint : ∀ s ∈ Icc a t, lhs s ≤ coefficient * outerMass s := by
    intro s hs
    have hs' : s ∈ Icc a t₁ := ⟨hs.1, hs.2.trans htt₁⟩
    have hmass_nonneg := evolvingLocalizedL2Mass_nonneg
      (I := I) (M := M) g cutoff u s
    have houter_nonneg := evolvingLocalizedL2Mass_nonneg
      (I := I) (M := M) g outer u s
    have hmass_le := evolvingLocalizedL2Mass_le_of_sq_le
      (I := I) (M := M) g cutoff outer hcutoff houter u hu s hcutoff_le
    have herror_le := evolvingCutoffGradientError_le_evolvingLocalizedL2Mass
      (I := I) (M := M) g cutoff outer hcutoff houter u hu s
        (hgrad s hs')
    have hdistortion_le := evolvingLocalizedVolumeDistortion_le
      (I := I) (M := M) g cutoff u s B (hg.at_any s)
        hcutoff.continuous
        (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous
        (htrace s hs')
    have htime := timeCutoff_mem_Icc a t₀ s
    have htime_term : timeCutoffDeriv a t₀ s * mass s ≤ D * outerMass s := by
      calc
        timeCutoffDeriv a t₀ s * mass s ≤ D * mass s :=
          mul_le_mul_of_nonneg_right (hderiv_le s hs') hmass_nonneg
        _ ≤ D * outerMass s := mul_le_mul_of_nonneg_left hmass_le hD
    have herror_term : timeCutoff a t₀ s * (4 * error s) ≤
        4 * K * outerMass s := by
      calc
        timeCutoff a t₀ s * (4 * error s) ≤ 1 * (4 * error s) :=
          mul_le_mul_of_nonneg_right htime.2
            (mul_nonneg (by norm_num)
              (evolvingCutoffGradientError_nonneg
                (I := I) (M := M) g cutoff u s))
        _ = 4 * error s := one_mul _
        _ ≤ 4 * (K * outerMass s) :=
          mul_le_mul_of_nonneg_left herror_le (by norm_num)
        _ = 4 * K * outerMass s := by ring
    have hdistortion_term : timeCutoff a t₀ s * distortion s ≤
        (1 / 2) * B * outerMass s := by
      calc
        timeCutoff a t₀ s * distortion s ≤
            timeCutoff a t₀ s * ((1 / 2) * B * mass s) :=
          mul_le_mul_of_nonneg_left hdistortion_le htime.1
        _ ≤ timeCutoff a t₀ s * ((1 / 2) * B * outerMass s) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmass_le
              (mul_nonneg (by norm_num) hB)) htime.1
        _ ≤ 1 * ((1 / 2) * B * outerMass s) :=
          mul_le_mul_of_nonneg_right htime.2
            (mul_nonneg (mul_nonneg (by norm_num) hB) houter_nonneg)
        _ = (1 / 2) * B * outerMass s := one_mul _
    dsimp only [lhs, coefficient, mass, error, distortion, outerMass]
    linarith
  have hmono : (∫ s in a..t, lhs s) ≤
      ∫ s in a..t, coefficient * outerMass s :=
    intervalIntegral.integral_mono_on hat hlhs_int hrhs_int hpoint
  have houter_inner : (∫ s in a..t, outerMass s) ≤
      ∫ s in a..t₁, outerMass s :=
    intervalIntegral.integral_mono_interval le_rfl hat htt₁
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact evolvingLocalizedL2Mass_nonneg
          (I := I) (M := M) g outer u s)
      houter_int
  calc
    (∫ s in a..t, lhs s) ≤ ∫ s in a..t, coefficient * outerMass s := hmono
    _ = coefficient * ∫ s in a..t, outerMass s := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ coefficient * ∫ s in a..t₁, outerMass s :=
      mul_le_mul_of_nonneg_left houter_inner hcoefficient
    _ ≤ coefficient * L :=
      mul_le_mul_of_nonneg_left
        (by simpa only [outerMass] using houterMass_le) hcoefficient
    _ = (D + 4 * K + (1 / 2) * B) * L := rfl

omit [I.Boundaryless] in
theorem evolvingLocalizedForcing_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : Continuous cutoff)
    (hu : Continuous (fun p : ℝ × M => u p.1 p.2))
    (hsource : Continuous (fun p : ℝ × M => source p.1 p.2)) :
    ContinuousOn
      (evolvingLocalizedForcing (I := I) (M := M) g cutoff u source) K := by
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact ((((continuous_const.mul
      ((hcutoff.comp continuous_snd).pow 2)).mul hu).mul hsource)).continuousOn

omit [I.Boundaryless] in
theorem deriv_evolvingLocalizedL2Mass_eq_deriv_localizedL2Mass_add_volume
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t =
      deriv (fun s => localizedL2Mass (I := I) (M := M)
        (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
        (smoothScalarSlice (I := I) (g t) u hu s)) t +
      ∫ x, cutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have hu_t : Continuous (u t) :=
    (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => u p.1 p.2, hu⟩
  have htime : Continuous (fun x : M => deriv (fun s => u s x) t) := by
    exact ((DifferentialGeometry.contMDiff_partial_deriv_fst I F).comp
      (contMDiff_const.prodMk contMDiff_id)).continuous
  have htrace_cont : Continuous
      (fun x : M => traceTimeDerivMetric (I := I) g t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hg
  have htime_int : Integrable (fun x : M =>
      2 * cutoff x ^ 2 * u t x * deriv (fun s => u s x) t) μ :=
    (((continuous_const.mul (hcutoff.continuous.pow 2)).mul hu_t).mul htime)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvolume_int : Integrable (fun x : M => cutoff x ^ 2 *
      ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)) μ :=
    ((hcutoff.continuous.pow 2).mul
      ((continuous_const.mul htrace_cont).mul (hu_t.pow 2)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [(hasDerivAt_evolvingLocalizedL2Mass
    (I := I) (M := M) g cutoff u t hg hcutoff hu).deriv]
  rw [(hasDerivAt_localizedL2Mass
    (I := I) (M := M) (⟨cutoff, hcutoff⟩ : SmoothScalar (g t)) u hu t).deriv]
  change (∫ x, cutoff x ^ 2 *
      (2 * u t x * deriv (fun s => u s x) t +
        (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2) ∂μ) =
    (∫ x, 2 * cutoff x ^ 2 * u t x * deriv (fun s => u s x) t ∂μ) +
      ∫ x, cutoff x ^ 2 *
        ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2) ∂μ
  rw [← integral_add htime_int hvolume_int]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem caccioppoli_differential_evolving
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x + source t x) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        ∫ x, cutoff x ^ 2 *
            ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  have hfixed := caccioppoli_differential
    (I := I) (M := M) (g := g t)
    (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
    u source hu hsource t hpde
  change deriv (fun s => localizedL2Mass (I := I) (M := M)
      (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
      (smoothScalarSlice (I := I) (g t) u hu s)) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) at hfixed
  rw [deriv_evolvingLocalizedL2Mass_eq_deriv_localizedL2Mass_add_volume
    (I := I) (M := M) g cutoff u t hg hcutoff hu]
  linarith

theorem caccioppoli_differential_evolving_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hu_nonneg : ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x + source t x) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        ∫ x, cutoff x ^ 2 *
            ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  have hfixed := caccioppoli_differential_of_subsolution
    (I := I) (M := M) (g := g t)
    (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
    u source hu hsource t hu_nonneg hpde
  change deriv (fun s => localizedL2Mass (I := I) (M := M)
      (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
      (smoothScalarSlice (I := I) (g t) u hu s)) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) at hfixed
  rw [deriv_evolvingLocalizedL2Mass_eq_deriv_localizedL2Mass_add_volume
    (I := I) (M := M) g cutoff u t hg hcutoff hu]
  linarith

theorem caccioppoli_differential_evolving_of_trace_le
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t B : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x + source t x)
    (htrace : ∀ x : M, traceTimeDerivMetric (I := I) g t x ≤ B) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        (1 / 2) * B * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff u t := by
  have henergy := caccioppoli_differential_evolving
    (I := I) (M := M) g cutoff u source t hg hcutoff hu hsource hpde
  change deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        evolvingLocalizedVolumeDistortion
          (I := I) (M := M) g cutoff u t at henergy
  have hvolume := evolvingLocalizedVolumeDistortion_le
    (I := I) (M := M) g cutoff u t B hg hcutoff.continuous
      (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous htrace
  linarith

theorem caccioppoli_differential_evolving_of_subsolution_of_trace_le
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t B : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hu_nonneg : ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x + source t x)
    (htrace : ∀ x : M, traceTimeDerivMetric (I := I) g t x ≤ B) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        (1 / 2) * B * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff u t := by
  have henergy := caccioppoli_differential_evolving_of_subsolution
    (I := I) (M := M) g cutoff u source t hg hcutoff hu hsource hu_nonneg hpde
  change deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        evolvingLocalizedVolumeDistortion
          (I := I) (M := M) g cutoff u t at henergy
  have hvolume := evolvingLocalizedVolumeDistortion_le
    (I := I) (M := M) g cutoff u t B hg hcutoff.continuous
      (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous htrace
  linarith

omit [I.Boundaryless] in
private theorem caccioppoli_evolving_of_differential
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
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
    (hdifferential : ∀ t ∈ Icc a b,
      deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
        4 * evolvingCutoffGradientError (I := I) (M := M) g cutoff u t +
          evolvingLocalizedForcing (I := I) (M := M) g cutoff u source t +
          evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u t) :
    weight b * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u b -
        weight a * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u a +
        ∫ t in a..b, weight t *
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
      ∫ t in a..b,
        dweight t * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff u t +
          weight t *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff u t +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff u source t +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff u t) := by
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u
  let dirichlet : ℝ → ℝ :=
    evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u
  let error : ℝ → ℝ :=
    evolvingCutoffGradientError (I := I) (M := M) g cutoff u
  let forcing : ℝ → ℝ :=
    evolvingLocalizedForcing (I := I) (M := M) g cutoff u source
  let distortion : ℝ → ℝ :=
    evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u
  have hmass_cont : ContinuousOn mass (Icc a b) := by
    simpa only [mass] using evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hcutoff.continuous hu.continuous
  have hdmass_cont : ContinuousOn (deriv mass) (Icc a b) := by
    simpa only [mass] using deriv_evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hcutoff hu
  have hmass_deriv : ∀ t ∈ Icc a b,
      HasDerivAt mass (deriv mass t) t := by
    intro t _
    have hraw := hasDerivAt_evolvingLocalizedL2Mass
      (I := I) (M := M) g cutoff u t (hg.at_any t) hcutoff hu
    simpa only [mass] using hraw.congr_deriv hraw.deriv.symm
  have hdirichlet : ContinuousOn dirichlet (Icc a b) := by
    simpa only [dirichlet] using evolvingLocalizedDirichletEnergy_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  have herror : ContinuousOn error (Icc a b) := by
    simpa only [error] using evolvingCutoffGradientError_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  have hforcing : ContinuousOn forcing (Icc a b) := by
    simpa only [forcing] using evolvingLocalizedForcing_continuousOn
      (I := I) (M := M) g cutoff u source isCompact_Icc hg
        hcutoff.continuous hu.continuous hsource.continuous
  have hdistortion : ContinuousOn distortion (Icc a b) := by
    simpa only [distortion] using evolvingLocalizedVolumeDistortion_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg
        hcutoff.continuous hu.continuous
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hdissipation : ContinuousOn
      (fun t => weight t * dirichlet t) (Icc a b) :=
    hweight_cont.mul hdirichlet
  have hrhs : ContinuousOn
      (fun t => dweight t * mass t +
        weight t * (4 * error t + forcing t + distortion t)) (Icc a b) :=
    (hdweight.mul hmass_cont).add
      (hweight_cont.mul
        (((continuousOn_const.mul herror).add hforcing).add hdistortion))
  have hpointwise : ∀ t ∈ Icc a b,
      dweight t * mass t + weight t * deriv mass t + weight t * dirichlet t ≤
        dweight t * mass t +
          weight t * (4 * error t + forcing t + distortion t) := by
    intro t ht
    have hmul := mul_le_mul_of_nonneg_left (hdifferential t ht)
      (hweight_nonneg t ht)
    change weight t * (deriv mass t + dirichlet t) ≤
      weight t * (4 * error t + forcing t + distortion t) at hmul
    linarith
  have hresult := weight_mul_energy_inequality
    hab hdweight hweight hdmass_cont hmass_deriv hdissipation hrhs hpointwise
  simpa only [mass, dirichlet, error, forcing, distortion] using hresult

theorem caccioppoli_evolving
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
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
      deriv (fun s => u s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x + source t x) :
    weight b * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u b -
        weight a * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u a +
        ∫ t in a..b, weight t *
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
      ∫ t in a..b,
        dweight t * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff u t +
          weight t *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff u t +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff u source t +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff u t) := by
  apply caccioppoli_evolving_of_differential
    (I := I) (M := M) g cutoff u source hcutoff hu hsource hg hgram
      hab hdweight hweight hweight_nonneg
  intro t ht
  have hraw := caccioppoli_differential_evolving
    (I := I) (M := M) g cutoff u source t (hg.at_any t)
      hcutoff hu hsource (hpde t ht)
  change deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
      evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
    4 * evolvingCutoffGradientError (I := I) (M := M) g cutoff u t +
      evolvingLocalizedForcing (I := I) (M := M) g cutoff u source t +
      evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u t at hraw
  exact hraw

theorem caccioppoli_evolving_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
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
    (hu_nonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x + source t x) :
    weight b * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u b -
        weight a * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u a +
        ∫ t in a..b, weight t *
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
      ∫ t in a..b,
        dweight t * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff u t +
          weight t *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff u t +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff u source t +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff u t) := by
  apply caccioppoli_evolving_of_differential
    (I := I) (M := M) g cutoff u source hcutoff hu hsource hg hgram
      hab hdweight hweight hweight_nonneg
  intro t ht
  have hraw := caccioppoli_differential_evolving_of_subsolution
    (I := I) (M := M) g cutoff u source t (hg.at_any t)
      hcutoff hu hsource (hu_nonneg t ht) (hpde t ht)
  change deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
      evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
    4 * evolvingCutoffGradientError (I := I) (M := M) g cutoff u t +
      evolvingLocalizedForcing (I := I) (M := M) g cutoff u source t +
      evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u t at hraw
  exact hraw

theorem caccioppoli_evolving_inner_energy_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {t : ℝ} (hg : MetricFamilyRegularAt (I := I) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {weight dweight : ℝ → ℝ} {a t₀ t₁ A : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hdweight : ContinuousOn dweight (Icc a t₁))
    (hweight : ∀ s ∈ Icc a t₁, HasDerivAt weight (dweight s) s)
    (hweight_nonneg : ∀ s ∈ Icc a t₁, 0 ≤ weight s)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ s ∈ Icc t₀ t₁, weight s = 1)
    (hu_nonneg : ∀ s ∈ Icc a t₁, ∀ x : M, 0 ≤ u s x)
    (hpde : ∀ s ∈ Icc a t₁, ∀ x : M,
      deriv (fun r => u r x) s ≤
        Δ_g (I := I) (g s)
          (smoothScalarSlice (I := I) (g s) u hu s).toContMDiffMap x + source s x)
    (hrhs_le : ∀ s ∈ Icc t₀ t₁,
      (∫ r in a..s,
        dweight r * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff u r +
          weight r *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff u r +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff u source r +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff u r)) ≤ A) :
    (∀ s ∈ Icc t₀ t₁,
      evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u s ≤ A) ∧
      (∫ s in t₀..t₁,
        evolvingLocalizedDirichletEnergy
          (I := I) (M := M) g cutoff u s) ≤ A := by
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u
  let dissipation : ℝ → ℝ :=
    evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u
  have hdirichlet : ContinuousOn dissipation (Icc a t₁) := by
    simpa only [dissipation] using evolvingLocalizedDirichletEnergy_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  let rhs : ℝ → ℝ := fun s =>
    dweight s * mass s +
      weight s *
        (4 * evolvingCutoffGradientError
            (I := I) (M := M) g cutoff u s +
          evolvingLocalizedForcing
            (I := I) (M := M) g cutoff u source s +
          evolvingLocalizedVolumeDistortion
            (I := I) (M := M) g cutoff u s)
  apply inner_mass_and_dissipation_le
    (weight := weight) (mass := mass) (dissipation := dissipation) (source := rhs)
    hat₀ ht₀t₁
  · intro s hs
    exact (hweight s hs).continuousAt.continuousWithinAt
  · simpa only [dissipation] using hdirichlet
  · exact hweight_nonneg
  · intro s _
    exact evolvingLocalizedDirichletEnergy_nonneg
      (I := I) (M := M) g cutoff u s
  · exact hweight_a
  · exact hweight_inner
  · intro s _
    exact evolvingLocalizedL2Mass_nonneg
      (I := I) (M := M) g cutoff u s
  · simpa only [rhs, mass] using hrhs_le
  · intro s hs
    have has : a ≤ s := hat₀.trans hs.1
    have hsubset : Icc a s ⊆ Icc a t₁ := fun r hr =>
      ⟨hr.1, hr.2.trans hs.2⟩
    have henergy := caccioppoli_evolving_of_subsolution
      (I := I) (M := M) g cutoff u source hcutoff hu hsource hg hgram
      has (hdweight.mono hsubset)
      (fun r hr => hweight r (hsubset hr))
      (fun r hr => hweight_nonneg r (hsubset hr))
      (fun r hr => hu_nonneg r (hsubset hr))
      (fun r hr => hpde r (hsubset hr))
    simpa only [mass, dissipation, rhs] using henergy

end DifferentialGeometry.Analysis.Parabolic.Energy
