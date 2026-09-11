import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.CovariantLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.WindowPullback

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem standard_closed_isSolutionOn (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime) (S : StandardSolution) :
    IsSolutionOn
      (S.val.toSolutionOn.timeRestrict (RealTimeInterval.closed 0 τ hτ.le)) := by
  have hlife : ENNReal.ofReal τ < S.val.lifetime :=
    hlt.trans_le (uniformStandardLifetime_le_lifetime S)
  apply isSolutionOn_timeRestrict S.val.isSolutionOn
  · exact (Icc_subset_lifetimeInterval_iff S.val.lifetime S.val.lifetime_pos τ hτ.le).mpr hlife
  · intro t ht
    change t ∈ Ioo 0 τ at ht
    exact (mem_lifetimeInterval_regular S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2.le).trans_lt hlife⟩

abbrev standardClosedPointedFlowSequence (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) : PointedFlowSeq (𝓡 3) where
  D := RealTimeInterval.closed 0 τ hτ.le
  term i := {
    M := E3
    basepoint := x i
    S := (S i).val.toSolutionOn.timeRestrict (RealTimeInterval.closed 0 τ hτ.le)
    isSolution := standard_closed_isSolutionOn τ hτ hlt (S i) }

@[simp] theorem standardClosedPointedFlowSequence_metric (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (i : ℕ) (t : ℝ) :
    ((standardClosedPointedFlowSequence τ hτ hlt S x).term i).S.base.metric t =
      (S i).val.metric t := rfl

@[simp] theorem standardClosedPointedFlowSequence_basepoint (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (i : ℕ) :
    ((standardClosedPointedFlowSequence τ hτ hlt S x).term i).basepoint = x i := rfl

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

theorem standardClosedPointedMaps_sourceSigma : SourceIsSigmaCompact Φ :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3) (Φ.source_open j)

theorem standardClosedPointedMaps_targetSigma : TargetIsSigmaCompact Φ :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3) (Φ.target_open j)

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

private theorem standard_closed_canonical_metric (j : ℕ) (t : ℝ) :
    sourceMetric Φ hsrc htgt j t =
      Diffeomorph.pullbackMetric
        (((S (φ j)).val.metric t).restrictOpen (targetOpen Φ j))
        (sourceTargetDiff Φ j) := rfl

private theorem standard_closed_transport_bounds
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (Λ : ℝ) (C L : ℕ → ℝ) (hC : ∀ N, 0 ≤ C N) (hL : ∀ N, 0 ≤ L N)
    (he : ∀ j, ∀ t ∈ Icc 0 τ,
      MetricUniformEquivalentOn univ ((S (φ j)).val.metric 0)
        ((S (φ j)).val.metric t) Λ)
    (hc : ∀ j N, ∀ t ∈ Icc 0 τ, ∀ z : E3,
      metricCovDerivNorm N ((S (φ j)).val.metric t)
        ((S (φ j)).val.metric 0) z ≤ C N)
    (hl : ∀ j N, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ z : E3,
      metricDerivNorm N ((S (φ j)).val.metric s) ((S (φ j)).val.metric t)
        ((S (φ j)).val.metric 0) z ≤ L N * |s - t|) :
    (∀ j,
      (∀ t ∈ Icc 0 τ,
        MetricUniformEquivalentOn univ (sourceMetricRestriction Φ P.metric j)
          (sourceMetric Φ hsrc htgt j t) Λ) ∧
      (∀ N, ∀ t ∈ Icc 0 τ, ∀ y : SourceDomain Φ j,
        metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t)
          (sourceMetricRestriction Φ P.metric j) y ≤ C N) ∧
      (∀ N, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ y : SourceDomain Φ j,
        metricDerivNorm N (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
          (sourceMetricRestriction Φ P.metric j) y ≤ L N * |s - t|)) ∧
      SourceMetricCovariantLipschitzBounds Φ P.metric hsrc htgt 0 τ := by
  have hcov (N j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (y : SourceDomain Φ j) :
      metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t) (sourceMetricRestriction Φ P.metric j) y ≤ C N := by
    rw [← hinit j, standard_closed_canonical_metric, standard_closed_canonical_metric,
      metricCovDerivNorm_pullback, covNorm_restrictOpen]
    exact hc j N t ht _
  have hlip (N j : ℕ) (s : ℝ) (hs : s ∈ Icc 0 τ)
      (t : ℝ) (ht : t ∈ Icc 0 τ) (y : SourceDomain Φ j) :
      metricDerivNorm N (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
        (sourceMetricRestriction Φ P.metric j) y ≤ L N * |s - t| := by
    rw [← hinit j, standard_closed_canonical_metric, standard_closed_canonical_metric,
      standard_closed_canonical_metric, metricDerivNorm_pullback, metricDerivNorm_restrictOpen]
    exact hl j N s hs t ht _
  constructor
  · intro j
    refine ⟨?_, fun N t ht y => hcov N j t ht y, fun N s hs t ht y => hlip N j s hs t ht y⟩
    intro t ht
    have hr := metricUniformEquivalentOn_restrictOpen univ
      ((S (φ j)).val.metric 0) ((S (φ j)).val.metric t) Λ (he j t ht)
      (targetOpen Φ j) (V := univ) (fun _ _ => mem_univ _)
    have hp := metricUniformEquivalentOn_pullback univ _ _ Λ hr
      (sourceTargetDiff Φ j) (V := univ) (fun _ _ => mem_univ _)
    rw [← standard_closed_canonical_metric Φ hsrc htgt,
      ← standard_closed_canonical_metric Φ hsrc htgt, hinit j] at hp
    exact hp
  · constructor
    · intro N
      exact ⟨C N, hC N, fun j t ht y => hcov N j t ht y⟩
    · intro N
      refine ⟨∑ a ∈ Finset.range (N + 1), L a,
        Finset.sum_nonneg (fun a _ => hL a), ?_⟩
      intro j s t hs ht a ha y
      refine (hlip a j s hs t ht y).trans
        (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      exact Finset.single_le_sum (s := Finset.range (N + 1)) (a := a) (f := L)
        (fun b _ => hL b) (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))

end Maps

theorem standard_closed_reference_bounds (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ (S : ℕ → StandardSolution) (x : ℕ → E3)
        (P : PointedRiemannianManifold (𝓡 3)) (φ : ℕ → ℕ)
        (Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x) P φ)
        (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ),
        (∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j) →
        letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace E3 P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold (𝓡 3) ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
        (∀ j,
          letI : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
          letI : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j
          letI : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
          letI : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
          letI : SigmaCompactSpace (SourceDomain Φ j) := sourceDomSigmaOf Φ j (hsrc j)
          (∀ t ∈ Icc 0 τ,
            MetricUniformEquivalentOn univ (sourceMetricRestriction Φ P.metric j)
              (sourceMetric Φ hsrc htgt j t) Λ) ∧
          (∀ N, ∀ t ∈ Icc 0 τ, ∀ y : SourceDomain Φ j,
            metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t)
              (sourceMetricRestriction Φ P.metric j) y ≤ C N) ∧
          (∀ N, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ y : SourceDomain Φ j,
            metricDerivNorm N (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
              (sourceMetricRestriction Φ P.metric j) y ≤ L N * |s - t|)) ∧
          SourceMetricCovariantLipschitzBounds Φ P.metric hsrc htgt 0 τ := by
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab τ hτ.le hlt
  obtain ⟨Λ, hΛ, C, L, hC, hL, hb⟩ :=
    standard_metric_bounds_on_shorter_windows τ K hτ.le hK
  refine ⟨Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S x P φ Φ hsrc htgt hinit
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace E3 P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold (𝓡 3) ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hactual (j : ℕ) :=
    hb (S (φ j)).val τ hτ.le le_rfl (hlife (S (φ j))) (hRm (S (φ j)))
  apply standard_closed_transport_bounds Φ hsrc htgt hinit Λ C L hC hL
  · intro j t ht
    rw [(S (φ j)).val.initial]
    exact (hactual j).1 t ht
  · intro j N t ht z
    rw [(S (φ j)).val.initial]
    exact (hactual j).2.1 N t ht z
  · intro j N s hs t ht z
    rw [(S (φ j)).val.initial]
    exact (hactual j).2.2 N s hs t ht z

end DifferentialGeometry.PDE.RicciFlow
