import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCapMetricBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoubleCharts
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import DifferentialGeometry.Topology.Exhaustion

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff BigOperators Topology
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩
private abbrev source (R : ℝ) : TopologicalSpace.Opens E3 :=
  ⟨Metric.ball 0 (R + 1), Metric.isOpen_ball⟩
private abbrev target (north : S3) (R : ℝ) : TopologicalSpace.Opens S3 :=
  ⟨compactDoubleCapPartialDiffeomorph north R '' (source R : Set E3),
    image_opens_isOpen (compactDoubleCapPartialDiffeomorph north R) (U := source R) subset_rfl⟩
private abbrev originalChart (north : S3) (R : ℝ) : source R ≃ₘ⟮𝓡 3, 𝓡 3⟯ target north R :=
  PartialDiffeomorph.toOpensDiffeo (compactDoubleCapPartialDiffeomorph north R)
    (U := source R) subset_rfl
private local instance (north : S3) (R : ℝ) : SigmaCompactSpace (target north R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (𝓡 3) (target north R).isOpen)
private def pulledMetric (north : S3) (R : ℝ) (g : SmoothRiemannianMetric (𝓡 3) S3) :
    SmoothRiemannianMetric (𝓡 3) (source R) :=
  Diffeomorph.pullbackMetric (g.restrictOpen (target north R)) (originalChart north R)
private def capReference (R : ℝ) : SmoothRiemannianMetric (𝓡 3) (source R) :=
  metric.restrictOpen (source R)

private theorem pulledMetric_inner (north : S3) (R : ℝ)
    (g : SmoothRiemannianMetric (𝓡 3) S3) (x : source R)
    (v w : TangentSpace (𝓡 3) x) :
    (pulledMetric north R g).inner x v w =
      g.inner (compactDoubleCapMap north R x.val)
        (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x.val v)
        (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x.val w) := by
  unfold pulledMetric
  rw [Diffeomorph.pullbackMetric_inner]
  change g.inner (compactDoubleCapPartialDiffeomorph north R x.val)
    (mfderiv (𝓡 3) (𝓡 3) (originalChart north R) x v)
    (mfderiv (𝓡 3) (𝓡 3) (originalChart north R) x w) = _
  dsimp only [TangentSpace] at v w ⊢
  erw [PartialDiffeomorph.mfderiv_toOpensDiffeo,
    PartialDiffeomorph.mfderiv_toOpensDiffeo]
  rfl

private theorem pulledMetric_initial (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) :
    pulledMetric north R (compactDoubleMetric north R hR) = capReference R := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [pulledMetric_inner]
  exact compactDoubleMetric_cap_pullback north R hR x.val x.property v w

private theorem pulled_spatial_norm (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R)
    (g : SmoothRiemannianMetric (𝓡 3) S3) (N : ℕ) (x : source R) :
    metricCovDerivNorm N (pulledMetric north R g) (capReference R) x =
      metricCovDerivNorm N g (compactDoubleMetric north R hR) (compactDoubleCapMap north R x.val) := by
  rw [← pulledMetric_initial north R hR]
  unfold pulledMetric
  rw [metricCovDerivNorm_pullback, covNorm_restrictOpen]
  rfl

private theorem pulled_time_norm (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R)
    (g h : SmoothRiemannianMetric (𝓡 3) S3) (N : ℕ) (x : source R) :
    metricDerivNorm N (pulledMetric north R g) (pulledMetric north R h) (capReference R) x =
      metricDerivNorm N g h (compactDoubleMetric north R hR) (compactDoubleCapMap north R x.val) := by
  rw [← pulledMetric_initial north R hR]
  unfold pulledMetric
  rw [metricDerivNorm_pullback, metricDerivNorm_restrictOpen]
  rfl

private theorem pulled_comparison (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) S3)
    (Λ : ℝ) (he : MetricUniformEquivalentOn univ (compactDoubleMetric north R hR) g Λ) :
    MetricUniformEquivalentOn univ (capReference R) (pulledMetric north R g) Λ := by
  refine ⟨he.1, ?_⟩
  intro x _ v
  have hh := he.2 (compactDoubleCapMap north R x.val) (mem_univ _)
    (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x.val v)
  rw [compactDoubleMetric_cap_pullback north R hR x.val x.property v v] at hh
  rw [pulledMetric_inner]
  exact hh

def compactCapApproximationRadius (j : ℕ) : ℝ := max transitionEnd 2 + 2 + j

theorem compactCapApproximationRadius_large (j : ℕ) : max transitionEnd 2 + 2 ≤ compactCapApproximationRadius j :=
  le_add_of_nonneg_right (Nat.cast_nonneg j)

abbrev compactCapPointedModel : PointedRiemannianManifold (𝓡 3) where
  M := E3
  basepoint := 0
  metric := metric
private theorem cap_balls_exhaust : ExhaustsByOpen (fun j => Metric.ball (0 : E3) (compactCapApproximationRadius j + 1)) where
  isOpen := fun _ => Metric.isOpen_ball
  mono_step := by
    intro j
    apply Metric.ball_subset_ball
    simp only [compactCapApproximationRadius, Nat.cast_add, Nat.cast_one]
    linarith
  subset := by
    intro K hK
    obtain ⟨r, hrK⟩ := hK.isBounded.subset_ball (0 : E3)
    obtain ⟨j₀, hj₀⟩ := exists_nat_gt (r - (max transitionEnd 2 + 2) - 1)
    refine ⟨j₀, ?_⟩
    intro j hj
    apply hrK.trans (Metric.ball_subset_ball ?_)
    have hcast : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    dsimp only [compactCapApproximationRadius]
    linarith

abbrev compactCapPointedFlowSequence {D : RealTimeInterval} (north : S3)
    (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j)) :
    PointedFlowSeq (𝓡 3) where
  D := D
  term j := {
    M := S3
    basepoint := compactDoubleCapMap north (compactCapApproximationRadius j) 0
    S := S j
    isSolution := hS j }

def compactCapPointedMaps {D : RealTimeInterval} (north : S3)
    (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j)) :
    PointedCGHMaps (compactCapPointedFlowSequence north S hS) compactCapPointedModel id where
  partialDiffeomorph j := compactDoubleCapPartialDiffeomorph north (compactCapApproximationRadius j)
  source_exhausts := cap_balls_exhaust
  base_mem := by
    intro j
    change (0 : E3) ∈ Metric.ball 0 (compactCapApproximationRadius j + 1)
    have hr : 0 < compactCapApproximationRadius j + 1 := by linarith [compactCapApproximationRadius_large j, le_max_right transitionEnd 2]
    simpa only [Metric.mem_ball, dist_self] using hr
  basepoint_map := fun _ => rfl

section Sequence
variable {D : RealTimeInterval} (north : S3)
  (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j))
private local instance (j : ℕ) : TopologicalSpace (SourceDomain (compactCapPointedMaps north S hS) j) :=
  sourceDomTop (compactCapPointedMaps north S hS) j
private local instance (j : ℕ) : ChartedSpace E3 (SourceDomain (compactCapPointedMaps north S hS) j) :=
  sourceDomCharted (compactCapPointedMaps north S hS) j
private local instance (j : ℕ) : T2Space (SourceDomain (compactCapPointedMaps north S hS) j) :=
  sourceDomT2 (compactCapPointedMaps north S hS) j
private local instance (j : ℕ) : IsManifold (𝓡 3) ∞ (SourceDomain (compactCapPointedMaps north S hS) j) :=
  sourceDomSmooth (compactCapPointedMaps north S hS) j
private theorem source_sigma : SourceIsSigmaCompact (compactCapPointedMaps north S hS) :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3) (PointedCGHMaps.source_open (compactCapPointedMaps north S hS) j)
private theorem target_sigma : TargetIsSigmaCompact (compactCapPointedMaps north S hS) :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3) (PointedCGHMaps.target_open (compactCapPointedMaps north S hS) j)
private local instance (j : ℕ) : SigmaCompactSpace (SourceDomain (compactCapPointedMaps north S hS) j) :=
  sourceDomSigmaOf (compactCapPointedMaps north S hS) j (source_sigma north S hS j)

private theorem actual_source_metric (j : ℕ) (t : ℝ) :
    sourceMetric (compactCapPointedMaps north S hS) (source_sigma north S hS) (target_sigma north S hS) j t =
      pulledMetric north (compactCapApproximationRadius j) ((S j).base.metric t) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  let data := SourceDomainMetricData.ofRestrictPullback
    (Φ := compactCapPointedMaps north S hS) (k := j) (source_sigma north S hS j)
    (fun _ => capReference (compactCapApproximationRadius j)) (fun _ => metric)
  let : TopologicalSpace (SourceDomain (compactCapPointedMaps north S hS) j) := data.topology
  let : ChartedSpace E3 (SourceDomain (compactCapPointedMaps north S hS) j) := data.charted
  let : T2Space (SourceDomain (compactCapPointedMaps north S hS) j) := data.t2
  let : IsManifold (𝓡 3) ∞ (SourceDomain (compactCapPointedMaps north S hS) j) := data.smooth
  let : SigmaCompactSpace (SourceDomain (compactCapPointedMaps north S hS) j) := data.sigmaCompact
  change (data.pullbackMetric t).inner x v w = _
  dsimp only [TangentSpace] at v w ⊢
  erw [data.pullback_inner]

private theorem actual_reference (j : ℕ) :
    sourceMetricRestriction (compactCapPointedMaps north S hS) metric j = capReference (compactCapApproximationRadius j) := rfl

private theorem closed_limit_data (τ : ℝ) (hτ : 0 ≤ τ)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (C L : ℕ → ℝ) (hC : ∀ N, 0 ≤ C N) (hL : ∀ N, 0 ≤ L N)
    (hzero : ∀ j, (S j).base.metric 0 = compactDoubleMetric north (compactCapApproximationRadius j) (compactCapApproximationRadius_large j))
    (he : ∀ j, ∀ t ∈ Icc 0 τ, MetricUniformEquivalentOn univ
      (compactDoubleMetric north (compactCapApproximationRadius j) (compactCapApproximationRadius_large j)) ((S j).base.metric t) Λ)
    (hspace : ∀ j N, ∀ t ∈ Icc 0 τ, ∀ x : S3,
      metricCovDerivNorm N ((S j).base.metric t)
        (compactDoubleMetric north (compactCapApproximationRadius j) (compactCapApproximationRadius_large j)) x ≤ C N)
    (htime : ∀ j N, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ x : S3,
      metricDerivNorm N ((S j).base.metric s) ((S j).base.metric t)
        (compactDoubleMetric north (compactCapApproximationRadius j) (compactCapApproximationRadius_large j)) x ≤ L N * |s - t|) :
    ∃ bf : BumpFamily (compactCapPointedMaps north S hS),
    ∃ cLow : ℝ, 0 < cLow ∧
    ∃ co : FlowMetricConvergenceData (compactCapPointedMaps north S hS) metric bf (source_sigma north S hS) (target_sigma north S hS) 0 τ,
      (∀ j t, t ∈ Icc 0 τ → ∀ (y : SourceDomain (compactCapPointedMaps north S hS) j)
        (v : TangentSpace (𝓡 3) y), cLow * metric.inner y.val v v ≤
          (sourceMetric (compactCapPointedMaps north S hS) (source_sigma north S hS)
            (target_sigma north S hS) j t).inner y v v) ∧
      (∀ q : ℕ, ∃ Cq : ℝ, ∀ j t, t ∈ Icc 0 τ → ∀ x ∈ bf.grow j,
        metricCovDerivNorm q (gSeqExt (compactCapPointedMaps north S hS) metric bf
          (source_sigma north S hS) (target_sigma north S hS) j t) metric x ≤ Cq) ∧
      co.gInf 0 = metric ∧
      (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (co.gInf t)) ∧
      ∀ K : Set E3, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
        ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
          metricDerivNorm a (co.gInf s) (co.gInf t) metric x ≤ Lp * |s - t| := by
  let Φ := compactCapPointedMaps north S hS
  let hsrc := source_sigma north S hS
  let htgt := target_sigma north S hS
  let bf : BumpFamily Φ := Classical.choice (nonempty_bumpFamily Φ)
  have hlow : 0 < Λ⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hΛ)
  have hbound (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ)
      (y : SourceDomain Φ j) (v : TangentSpace (𝓡 3) y) :
      Λ⁻¹ * metric.inner y.val v v ≤ (sourceMetric Φ hsrc htgt j t).inner y v v := by
    rw [actual_source_metric]
    exact ((pulled_comparison north (compactCapApproximationRadius j) (compactCapApproximationRadius_large j) _ Λ (he j t ht)).2 y (mem_univ y) v).1
  have hcov (N j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (y : SourceDomain Φ j) :
      metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t) (sourceMetricRestriction Φ metric j) y ≤ C N := by
    rw [actual_source_metric, actual_reference]
    erw [pulled_spatial_norm north (compactCapApproximationRadius j) (compactCapApproximationRadius_large j)]
    exact hspace j N t ht _
  have hlip (p : ℕ) : ∃ Lp : ℝ, 0 ≤ Lp ∧
      ∀ (j : ℕ) (s t : ℝ), s ∈ Icc 0 τ → t ∈ Icc 0 τ → ∀ a : ℕ, a ≤ p →
        ∀ y : SourceDomain Φ j,
          metricDerivNorm a (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
            (sourceMetricRestriction Φ metric j) y ≤ Lp * |s - t| := by
    refine ⟨∑ a ∈ Finset.range (p + 1), L a, Finset.sum_nonneg (fun a _ => hL a), ?_⟩
    intro j s t hs ht a ha y
    rw [actual_source_metric, actual_source_metric, actual_reference]
    erw [pulled_time_norm north (compactCapApproximationRadius j) (compactCapApproximationRadius_large j)]
    refine (htime j a s hs t ht _).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    exact Finset.single_le_sum (s := Finset.range (p + 1)) (a := a) (f := L)
      (fun b _ => hL b) (Finset.mem_range.mpr (by omega))
  have hcovTail := covTail_of_bounds Φ metric bf hsrc htgt 0 τ
    (fun q => ⟨C q, hC q, fun j t ht y _ => hcov q j t ht y⟩)
  have hlipTail := lipTail_of_source Φ metric bf hsrc htgt 0 τ (by
    intro p
    obtain ⟨Lp, hLp, hh⟩ := hlip p
    exact ⟨Lp, hLp, fun j s t hs ht a ha y _ => hh j s t hs ht a ha y⟩)
  have hlipSrc (j : ℕ) (K : Set (SourceDomain Φ j)) (_hK : IsCompact K) (p : ℕ) :
      ∃ Lp : ℝ, 0 ≤ Lp ∧ ∀ s t : ℝ, s ∈ Icc 0 τ → t ∈ Icc 0 τ →
        ∀ a : ℕ, a ≤ p → ∀ y ∈ K,
          metricDerivNorm a (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
            (sourceMetricRestriction Φ metric j) y ≤ Lp * |s - t| := by
    obtain ⟨Lp, hLp, hh⟩ := hlip p
    exact ⟨Lp, hLp, fun s t hs ht a ha y _ => hh j s t hs ht a ha y⟩
  let co := flowMetricConvergenceData Φ metric bf hsrc htgt 0 τ hτ Λ⁻¹ hlow hbound hcovTail hlipTail hlipSrc
  have hseq := gSeqExt_lower Φ metric bf hsrc htgt Λ⁻¹ 0 τ hlow hbound
  refine ⟨bf, Λ⁻¹, hlow, co, hbound, hcovTail, ?_, ?_, ?_⟩
  · apply gInf_zero_eq Φ metric bf hsrc htgt 0 τ co ⟨le_rfl, hτ⟩ metric
    intro x v w ε hε
    refine ⟨0, fun j _ hx => ?_⟩
    rw [actual_source_metric, hzero j, pulledMetric_initial]
    change |metric.inner x v w - metric.inner x v w| < ε
    simpa only [sub_self, abs_zero] using hε
  · intro t ht
    exact ⟨co.complete_at Φ metric_complete.complete (lt_min hlow zero_lt_one)
      (fun j r hr x v => hseq (co.φ j) r hr x v) ht⟩
  · intro K hK p
    obtain ⟨Lp, hLp, hseqLip⟩ := hgLip_gSeqExt Φ metric bf hsrc htgt 0 τ hlipTail hlipSrc K hK p
    refine ⟨Lp, hLp, ?_⟩
    apply metric_limit_derivative_norm_lipschitz K 0 τ p (gSeqExt Φ metric bf hsrc htgt) co.gInf metric co.φ Lp hseqLip
    intro t ht ε hε
    obtain ⟨j₀, hj₀⟩ := co.convergencePt K hK p ε hε
    exact ⟨j₀, fun j hj a ha x hx => hj₀ j hj t ht a ha x hx⟩
end Sequence

private theorem closed_gram_jets_of_time_bounds
    (τ : ℝ) (g : ℝ → SmoothRiemannianMetric (𝓡 3) E3)
    (hlip : ∀ K : Set E3, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
      ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
        metricDerivNorm a (g s) (g t) metric x ≤ Lp * |s - t|) :
    ∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContinuousOn
        (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (Icc 0 τ ×ˢ interior (extChartAt (𝓡 3) x₀).target) := by
  intro r x₀ i j p₀ hp₀
  obtain ⟨C, hCc, hCint, hCsub⟩ := exists_compact_subset isOpen_interior hp₀.2
  have hCtgt : C ⊆ (extChartAt (𝓡 3) x₀).target := hCsub.trans interior_subset
  let K : Set E3 := (extChartAt (𝓡 3) x₀).symm '' C
  have hKc : IsCompact K :=
    hCc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := 𝓡 3) x₀).mono hCtgt)
  have hKchart : K ⊆ (chartAt E3 x₀).source := by
    rintro y ⟨z, hz, rfl⟩
    rw [← extChartAt_source_eq_chartAt_source (I := 𝓡 3)]
    exact (extChartAt (𝓡 3) x₀).map_target (hCtgt hz)
  obtain ⟨Cjet, hCjet, hjet⟩ := chartJet_sub_le metric x₀ hKc hKchart r
  obtain ⟨Lp, hLp, hb⟩ := hlip K hKc r
  let A := Cjet * ((r + 1 : ℕ) : ℝ) * Lp
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcOn : ContinuousOn
      (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
      (Icc 0 τ ×ˢ C) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ ⟨A, hA⟩
    · intro t _ z hz
      have hh := (chartGramOnE_contDiffOn (I := 𝓡 3) (g t) x₀ i j).mono interior_subset
      exact ((hh.contDiffAt (isOpen_interior.mem_nhds (hCsub hz))).continuousAt_iteratedFDeriv
        (WithTop.coe_le_coe.2 (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousWithinAt
    · intro z hz
      apply LipschitzOnWith.of_dist_le_mul
      intro s hs t ht
      let y : E3 := (extChartAt (𝓡 3) x₀).symm z
      have hyK : y ∈ K := ⟨z, hz, rfl⟩
      have hright : extChartAt (𝓡 3) x₀ y = z := (extChartAt (𝓡 3) x₀).right_inv (hCtgt hz)
      rw [dist_eq_norm, Real.dist_eq]
      change ‖iteratedFDeriv ℝ r (chartGramOnE (g s) x₀ i j) z -
        iteratedFDeriv ℝ r (chartGramOnE (g t) x₀ i j) z‖ ≤ A * |s - t|
      have hh := hjet (g s) (g t) y hyK i j
      rw [hright] at hh
      refine hh.trans ?_
      calc
        Cjet * ∑ q ∈ Finset.range (r + 1), metricDerivNorm q (g s) (g t) metric y
            ≤ Cjet * ∑ _q ∈ Finset.range (r + 1), Lp * |s - t| := by
              apply mul_le_mul_of_nonneg_left _ hCjet
              exact Finset.sum_le_sum (fun q hq => hb s hs t ht q
                (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)) y hyK)
        _ = A * |s - t| := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          dsimp only [A]
          ring
  have hmem : Icc 0 τ ×ˢ C ∈ 𝓝[Icc 0 τ ×ˢ interior (extChartAt (𝓡 3) x₀).target] p₀ := by
    have hnhds : (univ ×ˢ interior C : Set (ℝ × E3)) ∈ 𝓝 p₀ :=
      prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hCint)
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hnhds) ?_
    rintro ⟨t, z⟩ ⟨⟨ht, _⟩, _, hzC⟩
    exact ⟨ht, interior_subset hzC⟩
  exact (hcOn.continuousWithinAt ⟨hp₀.1, interior_subset hCint⟩).mono_of_mem_nhdsWithin hmem

theorem exists_complete_closed_cap_limit_data :
    ∃ τ : ℝ, ∃ hτ : 0 < τ, ∃ B : ℕ → ℝ, (∀ N, 0 ≤ B N) ∧ ∀ north : S3,
    ∃ S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le),
    ∃ hS : ∀ j, IsSolutionOn (S j),
      (∀ j, (S j).base.metric 0 = compactDoubleMetric north (compactCapApproximationRadius j)
        (compactCapApproximationRadius_large j)) ∧
      (∀ j, ∀ t ∈ Icc 0 τ, RiemannianMetricComplete ((S j).base.metric t)) ∧
      (∀ j (x₀ : S3) (i k : Fin (Module.finrank ℝ E3)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix ((S j).base.metric p.1) x₀ p.2 i k)
          (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
      (∀ j, ∀ t ∈ Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
        HasDerivWithinAt (fun r => ((S j).base.metric r).inner x v w)
          (-2 * ricciTensor ((S j).base.metric t) x v w) (Ici 0) t) ∧
      (∀ N j a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ Icc 0 τ, ∀ x : S3,
        Real.sqrt (normSq0S ((S j).base.metric t) x (4 + a)
          (iteratedCovariantTimeDerivWithin (S j).base.metric
            (fun r => nablaKRm04Field (S j) r a x) (Icc 0 τ) b t)) ≤ B N) ∧
      ∃ bf : BumpFamily (compactCapPointedMaps north S hS),
      ∃ hsrc : SourceIsSigmaCompact (compactCapPointedMaps north S hS),
      ∃ htgt : TargetIsSigmaCompact (compactCapPointedMaps north S hS),
      ∃ cLow : ℝ, 0 < cLow ∧
      ∃ co : FlowMetricConvergenceData (compactCapPointedMaps north S hS) metric bf hsrc htgt 0 τ,
        (∀ j t, t ∈ Icc 0 τ →
          letI : TopologicalSpace (SourceDomain (compactCapPointedMaps north S hS) j) :=
            sourceDomTop (compactCapPointedMaps north S hS) j
          letI : ChartedSpace E3 (SourceDomain (compactCapPointedMaps north S hS) j) :=
            sourceDomCharted (compactCapPointedMaps north S hS) j
          letI : IsManifold (𝓡 3) ∞ (SourceDomain (compactCapPointedMaps north S hS) j) :=
            sourceDomSmooth (compactCapPointedMaps north S hS) j
          ∀ (y : SourceDomain (compactCapPointedMaps north S hS) j) (v : TangentSpace (𝓡 3) y),
            cLow * metric.inner y.val v v ≤
              (sourceMetric (compactCapPointedMaps north S hS) hsrc htgt j t).inner y v v) ∧
        (∀ q : ℕ, ∃ Cq : ℝ, ∀ j t, t ∈ Icc 0 τ → ∀ x ∈ bf.grow j,
          metricCovDerivNorm q (gSeqExt (compactCapPointedMaps north S hS) metric bf hsrc htgt j t)
            metric x ≤ Cq) ∧
        co.gInf 0 = metric ∧ (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (co.gInf t)) ∧
        (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (co.gInf p.1) x₀ p.2 i j)
            (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
        (∀ t ∈ Ioo 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
          HasDerivAt (fun s => (co.gInf s).inner x v w) (-2 * ricciTensor (co.gInf t) x v w) t) ∧
        ∀ K : Set E3, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
          ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
            metricDerivNorm a (co.gInf s) (co.gInf t) metric x ≤ Lp * |s - t| := by
  obtain ⟨τ, hτ, Λ, hΛ, B, C, L, hB, hC, hL, hflows⟩ := exists_uniform_compact_cap_metric_bounds
  refine ⟨τ, hτ, B, hB, ?_⟩
  intro north
  choose S hS hzero hcomplete hgram hpde hRm he hspace htime using
    (fun j : ℕ => hflows north (compactCapApproximationRadius j) (compactCapApproximationRadius_large j))
  obtain ⟨bf, cLow, hcLow, co, hbound, hcovTail, hinit, hlimcomplete, hlip⟩ := closed_limit_data north S hS τ hτ.le
    Λ hΛ C L hC hL hzero he hspace htime
  refine ⟨S, hS, hzero, hcomplete, hgram, hpde, (fun N j => hRm j N),
    bf, source_sigma north S hS, target_sigma north S hS, cLow, hcLow, co,
    hbound, hcovTail, hinit, hlimcomplete, ?_, ?_, hlip⟩
  · exact co.gramSmoothIcc (compactCapPointedMaps north S hS) hτ subset_rfl subset_rfl
      (closed_gram_jets_of_time_bounds τ co.gInf hlip)
  · intro t ht x v w
    exact co.metricPDE_regular (compactCapPointedMaps north S hS) subset_rfl ht x v w

theorem exists_complete_closed_cap_metric_limit :
    ∃ τ : ℝ, 0 < τ ∧ ∀ _north : S3,
      ∃ g : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
        g 0 = metric ∧ (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (g t)) ∧
        (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
            (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
        (∀ t ∈ Ioo 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
          HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) ∧
        ∀ K : Set E3, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
          ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
            metricDerivNorm a (g s) (g t) metric x ≤ Lp * |s - t| := by
  obtain ⟨τ, hτ, B, _, hdata⟩ := exists_complete_closed_cap_limit_data
  refine ⟨τ, hτ, ?_⟩
  intro north
  obtain ⟨S, hS, _, _, _, _, _, bf, hsrc, htgt, cLow, _, co, _, _, hzero, hc, hg, hpde, hlip⟩ := hdata north
  exact ⟨co.gInf, hzero, hc, hg, hpde, hlip⟩
end DifferentialGeometry.PDE.RicciFlow
