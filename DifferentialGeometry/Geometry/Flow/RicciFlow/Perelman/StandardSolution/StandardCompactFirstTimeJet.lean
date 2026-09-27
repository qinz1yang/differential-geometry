import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedLimitRicciLipschitz
import DifferentialGeometry.Analysis.Calculus.Derivative.ForwardTimeDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedMetricLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

section Maps

variable {τ : ℝ} {hτ : 0 < τ} {hlt : ENNReal.ofReal τ < uniformStandardLifetime}
  {S : ℕ → StandardSolution} {x : ℕ → E3}
  {P : PointedRiemannianManifold (𝓡 3)} {φ : ℕ → ℕ}
  (Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x) P φ)

private local instance : TopologicalSpace P.M := P.topology
private local instance : ChartedSpace E3 P.M := P.charted
private local instance : T2Space P.M := P.t2
private local instance : IsManifold (𝓡 3) ∞ P.M := P.smooth
private local instance : SigmaCompactSpace P.M := P.sigmaCompact
private local instance : IsManifold (𝓡 3) 1 P.M :=
  IsManifold.of_le (I := 𝓡 3) (M := P.M) (n := ∞) (by decide)

variable (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)

private local instance (j : ℕ) : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
private local instance (j : ℕ) : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j
private local instance (j : ℕ) : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
private local instance (j : ℕ) : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
private local instance (j : ℕ) : SigmaCompactSpace (SourceDomain Φ j) :=
  sourceDomSigmaOf Φ j (standardClosedPointedMaps_sourceSigma Φ j)
private local instance (j : ℕ) : TopologicalSpace (TargetDomain Φ j) := targetDomTop Φ j
private local instance (j : ℕ) : ChartedSpace E3 (TargetDomain Φ j) := targetDomCharted Φ j
private local instance (j : ℕ) : T2Space (TargetDomain Φ j) := targetDomT2 Φ j
private local instance (j : ℕ) : IsManifold (𝓡 3) ∞ (TargetDomain Φ j) := targetDomSmooth Φ j
private local instance (j : ℕ) : SigmaCompactSpace (TargetDomain Φ j) :=
  targetDomSigmaOf Φ j (standardClosedPointedMaps_targetSigma Φ j)

private theorem source_right_equation
    (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ)
    (q : SourceDomain Φ j) (v w : TangentSpace (𝓡 3) q) :
    HasDerivWithinAt (fun s => (sourceMetric Φ hsrc htgt j s).inner q v w)
      (-2 * ricciTensor (sourceMetric Φ hsrc htgt j t) q v w) (Ici 0) t := by
  have htime : t ∈ (S (φ j)).val.domain :=
    (Icc_subset_lifetimeInterval_iff (S (φ j)).val.lifetime
      (S (φ j)).val.lifetime_pos τ hτ.le).mpr
        (hlt.trans_le (uniformStandardLifetime_le_lifetime (S (φ j)))) ht
  change HasDerivWithinAt
    (fun s => (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric s).restrictOpen (targetOpen Φ j))
      (sourceTargetDiff Φ j)).inner q v w)
    (-2 * ricciTensor (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric t).restrictOpen (targetOpen Φ j))
      (sourceTargetDiff Φ j)) q v w) (Ici 0) t
  simp_rw [Diffeomorph.pullbackMetric_inner, CheegerGromovCompactness.ricciTensor_pullback,
    DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen,
    SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
  exact (S (φ j)).val.equation t htime _ _ _

private theorem value_error_of_canonical_sup
    (j : ℕ) (K : Set P.M) (hK : IsCompact K) (hKsrc : K ⊆ Φ.source j)
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) P.M) (t η : ℝ) (hη : 0 ≤ η)
    (herr : (SourceDomainMetricData.ofRestrictPullback
      (Φ := Φ) (k := j) (hsrc j) (fun _ => sourceMetricRestriction Φ P.metric j) g).derivNormSupOn
        (I := 𝓡 3) K 0 t < η)
    (q : P.M) (hq : q ∈ K) (v w : TangentSpace (𝓡 3) q)
    (hv : P.metric.inner q v v ≤ 1) (hw : P.metric.inner q w w ≤ 1) :
    |(sourceMetric Φ hsrc htgt j t).inner ⟨q, hKsrc hq⟩ v w - (g t).inner q v w| ≤ η := by
  let qs : SourceDomain Φ j := ⟨q, hKsrc hq⟩
  have hcompact : IsCompact (sourceCompactSet Φ j K) :=
    sourceCompactSet_isCompact Φ j hK hKsrc
  have hqs : qs ∈ sourceCompactSet Φ j K := hq
  have hs : metricDerivNormSupOn (sourceCompactSet Φ j K) 0
      (sourceMetric Φ hsrc htgt j t) (sourceMetricRestriction Φ (g t) j)
        (sourceMetricRestriction Φ P.metric j) < η := by
    exact herr
  have hn := (derivNorm_le_sup hcompact (le_refl 0)
    (sourceMetric Φ hsrc htgt j t) (sourceMetricRestriction Φ (g t) j)
      (sourceMetricRestriction Φ P.metric j) hqs).trans_lt hs
  have hpair := metricDifference_abs_le (sourceMetric Φ hsrc htgt j t)
    (sourceMetricRestriction Φ (g t) j) (sourceMetricRestriction Φ P.metric j) qs v w
  have hres : (sourceMetricRestriction Φ (g t) j).inner qs v w = (g t).inner q v w := rfl
  rw [hres] at hpair
  have hsv : Real.sqrt ((sourceMetricRestriction Φ P.metric j).inner qs v v) ≤ 1 := by
    change Real.sqrt (P.metric.inner q v v) ≤ 1
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hv
  have hsw : Real.sqrt ((sourceMetricRestriction Φ P.metric j).inner qs w w) ≤ 1 := by
    change Real.sqrt (P.metric.inner q w w) ≤ 1
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hw
  have hfactor : Real.sqrt ((sourceMetricRestriction Φ P.metric j).inner qs v v) *
      Real.sqrt ((sourceMetricRestriction Φ P.metric j).inner qs w w) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hsv hsw (Real.sqrt_nonneg _) zero_le_one
  calc |(sourceMetric Φ hsrc htgt j t).inner ⟨q, hKsrc hq⟩ v w - (g t).inner q v w|
      ≤ metricDerivNorm 0 (sourceMetric Φ hsrc htgt j t) (sourceMetricRestriction Φ (g t) j)
          (sourceMetricRestriction Φ P.metric j) qs *
            Real.sqrt ((sourceMetricRestriction Φ P.metric j).inner qs v v) *
              Real.sqrt ((sourceMetricRestriction Φ P.metric j).inner qs w w) := hpair
    _ ≤ η * Real.sqrt ((sourceMetricRestriction Φ P.metric j).inner qs v v) *
        Real.sqrt ((sourceMetricRestriction Φ P.metric j).inner qs w w) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hn.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ ≤ η * 1 := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfactor hη
    _ = η := by ring

theorem standard_closed_source_first_time_jet_converges_on_compacts
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (bf : BumpFamily Φ) (co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ)
    (hgram : ∀ (q : P.M) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × P.M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (co.gInf p.1) q p.2 i j)
        (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet))
    (hpde : ∀ t ∈ Ioo 0 τ, ∀ (q : P.M) (v w : TangentSpace (𝓡 3) q),
      HasDerivAt (fun s => (co.gInf s).inner q v w)
        (-2 * ricciTensor (co.gInf t) q v w) t)
    (θ : ℝ) (hθτ : θ < τ) (K : Set P.M) (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∃ hKsrc : K ⊆ Φ.source (co.φ k),
        ∀ (q : P.M) (hq : q ∈ K) (v w : TangentSpace (𝓡 3) q),
          P.metric.inner q v v ≤ 1 → P.metric.inner q w w ≤ 1 →
          ∀ t ∈ Icc 0 θ,
            HasDerivWithinAt
              (fun s => (sourceMetric Φ hsrc htgt (co.φ k) s).inner ⟨q, hKsrc hq⟩ v w)
              (-2 * ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) t) ⟨q, hKsrc hq⟩ v w)
              (Ici 0) t ∧
            HasDerivWithinAt (fun s => (co.gInf s).inner q v w)
              (-2 * ricciTensor (co.gInf t) q v w) (Ici 0) t ∧
            |derivWithin
                (fun s => (sourceMetric Φ hsrc htgt (co.φ k) s).inner ⟨q, hKsrc hq⟩ v w)
                (Ici 0) t -
              derivWithin (fun s => (co.gInf s).inner q v w) (Ici 0) t| < ε := by
  obtain ⟨L, hL, hsource, hlimit⟩ :=
    standard_closed_source_limit_ricci_lipschitz Φ hsrc htgt hinit bf co
  let M : ℝ := 2 * L
  have hM : 0 ≤ M := mul_nonneg (by norm_num) hL
  intro ε hε
  let h : ℝ := min ((τ - θ) / 2) (ε / (8 * (M + 1)))
  have hden : 0 < 8 * (M + 1) := by positivity
  have hh : 0 < h := lt_min (by positivity) (div_pos hε hden)
  have hmargin : h ≤ (τ - θ) / 2 := min_le_left _ _
  have hsmall : h ≤ ε / (8 * (M + 1)) := min_le_right _ _
  have hMh : 2 * M * h ≤ ε / 4 := by
    have hm := (le_div_iff₀ hden).mp hsmall
    nlinarith
  let η : ℝ := ε * h / 8
  have hη : 0 < η := by positivity
  obtain ⟨kc, hkc⟩ := ofRP_supOn_convergence Φ P.metric bf hsrc htgt
    0 τ co co.gInf (fun _ _ => rfl) K hK 0 η hη
  obtain ⟨kg, hkg⟩ := bf.grow_cover K hK
  refine ⟨max kc kg, ?_⟩
  intro k hk
  have hkconv : kc ≤ k := (le_max_left kc kg).trans hk
  have hKgrow : K ⊆ bf.grow (co.φ k) :=
    hkg (co.φ k) (((le_max_right kc kg).trans hk).trans (co.strictMono.id_le k))
  have hKsrc : K ⊆ Φ.source (co.φ k) := hKgrow.trans (bf.grow_subset (co.φ k))
  refine ⟨hKsrc, ?_⟩
  intro q hq v w hv hw
  let qs : SourceDomain Φ (co.φ k) := ⟨q, hKsrc hq⟩
  let f : ℝ → ℝ := fun r => (sourceMetric Φ hsrc htgt (co.φ k) r).inner qs v w
  let f' : ℝ → ℝ := fun r => -2 * ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) r) qs v w
  let g : ℝ → ℝ := fun r => (co.gInf r).inner q v w
  let g' : ℝ → ℝ := fun r => -2 * ricciTensor (co.gInf r) q v w
  have hfdAll (r : ℝ) (hr : r ∈ Icc 0 τ) : HasDerivWithinAt f (f' r) (Ici 0) r :=
    source_right_equation Φ hsrc htgt (co.φ k) r hr qs v w
  have hfc : ContinuousOn f (Icc 0 τ) := fun r hr =>
    (hfdAll r hr).continuousWithinAt.mono Icc_subset_Ici_self
  have hfd : ∀ r ∈ Ico 0 τ, HasDerivWithinAt f (f' r) (Ici 0) r :=
    fun r hr => hfdAll r ⟨hr.1, hr.2.le⟩
  have hgc : ContinuousOn g (Icc 0 τ) := by
    exact (tensor0SEvalCLM (I := 𝓡 3) (vec2 v w)).continuous.comp_continuousOn
      (metricCovDeriv_contDiffOn_time co.gInf (Icc 0 τ) hgram P.metric 0 q).continuousOn
  have hgd (r : ℝ) (hr : r ∈ Ico 0 τ) : HasDerivWithinAt g (g' r) (Ici 0) r := by
    rcases eq_or_lt_of_le hr.1 with heq | hpos
    · subst r
      exact metric_right_derivative_of_closed_gram hτ co.gInf hgram hpde q v w
    · exact (hpde r ⟨hpos, hr.2⟩ q v w).hasDerivWithinAt
  have hsv : Real.sqrt (P.metric.inner q v v) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hv
  have hsw : Real.sqrt (P.metric.inner q w w) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hw
  have hprod : Real.sqrt (P.metric.inner q v v) * Real.sqrt (P.metric.inner q w w) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hsv hsw (Real.sqrt_nonneg _) zero_le_one
  have hunit (d : ℝ) (hd : 0 ≤ d) :
      L * Real.sqrt (P.metric.inner q v v) * Real.sqrt (P.metric.inner q w w) * d ≤ L * d := by
    have hz := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hL) hd
    simpa only [mul_one, mul_assoc] using hz
  have hfl (s : ℝ) (hs : s ∈ Icc 0 τ) (t : ℝ) (ht : t ∈ Icc 0 τ) :
      |f' s - f' t| ≤ M * |s - t| := by
    have hr := (hsource (co.φ k) s hs t ht qs v w).trans (hunit |s - t| (abs_nonneg _))
    have hh2 := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)
    change |-2 * ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) s) qs v w -
      (-2 * ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) t) qs v w)| ≤ _
    rw [← mul_sub, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    simpa only [M, mul_assoc] using hh2
  have hgl (s : ℝ) (hs : s ∈ Icc 0 τ) (t : ℝ) (ht : t ∈ Icc 0 τ) :
      |g' s - g' t| ≤ M * |s - t| := by
    have hr := (hlimit s hs t ht q v w).trans (hunit |s - t| (abs_nonneg _))
    have hh2 := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)
    change |-2 * ricciTensor (co.gInf s) q v w - (-2 * ricciTensor (co.gInf t) q v w)| ≤ _
    rw [← mul_sub, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    simpa only [M, mul_assoc] using hh2
  have hval (r : ℝ) (hr : r ∈ Icc 0 τ) : |f r - g r| ≤ η :=
    value_error_of_canonical_sup Φ hsrc htgt (co.φ k) K hK hKsrc co.gInf r η hη.le
      (hkc k hkconv r hr) q hq v w hv hw
  intro t ht
  have hforward : t + h ≤ τ := by linarith [ht.2]
  have herr := DifferentialGeometry.Analysis.right_derivative_error_le_of_value_error
    f f' g g' τ M η hM hfc hgc hfd hgd hfl hgl hval t h ht.1 hh hforward
  have hcancel : 2 * η / h = ε / 4 := by
    calc 2 * η / h = ((ε / 4) * h) / h := by dsimp only [η]; ring
      _ = ε / 4 := mul_div_cancel_right₀ _ hh.ne'
  rw [hcancel] at herr
  have hstrict : |f' t - g' t| < ε := herr.trans_lt (by linarith)
  have hdsrc := hfdAll t ⟨ht.1, ht.2.trans hθτ.le⟩
  have hdlim := hgd t ⟨ht.1, ht.2.trans_lt hθτ⟩
  refine ⟨hdsrc, hdlim, ?_⟩
  rw [hdsrc.derivWithin (uniqueDiffOn_Ici 0 t ht.1),
    hdlim.derivWithin (uniqueDiffOn_Ici 0 t ht.1)]
  exact hstrict

end Maps
end DifferentialGeometry.PDE.RicciFlow

end
