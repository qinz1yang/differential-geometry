import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoubleCoreCharts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCapMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.CovariantLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.WindowPullback
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

theorem compactCapCoreApproximationRadius_large (j : ℕ) :
    transitionEnd + 4 ≤ compactCapApproximationRadius (j + 2) := by
  have hm := le_max_left transitionEnd 2
  simp only [compactCapApproximationRadius, Nat.cast_add, Nat.cast_ofNat]
  linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]

private theorem core_balls_exhaust : ExhaustsByOpen
    (fun j => Metric.ball (0 : E3) (compactCapApproximationRadius (j + 2) - 2)) where
  isOpen := fun _ => Metric.isOpen_ball
  mono_step := by
    intro j
    apply Metric.ball_subset_ball
    simp only [compactCapApproximationRadius, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith
  subset := by
    intro K hK
    obtain ⟨r, hrK⟩ := hK.isBounded.subset_ball (0 : E3)
    obtain ⟨j₀, hj₀⟩ := exists_nat_gt (r - (max transitionEnd 2 + 2))
    refine ⟨j₀, ?_⟩
    intro j hj
    apply hrK.trans (Metric.ball_subset_ball ?_)
    have hcast : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    simp only [compactCapApproximationRadius, Nat.cast_add, Nat.cast_ofNat]
    linarith

abbrev compactCorePointedModel (g : SmoothRiemannianMetric (𝓡 3) E3) :
    PointedRiemannianManifold (𝓡 3) where
  M := E3
  basepoint := 0
  metric := g

abbrev compactCorePointedFlowSequence {D : RealTimeInterval} (north : S3)
    (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j)) :
    PointedFlowSeq (𝓡 3) where
  D := D
  term j := {
    M := S3
    basepoint := compactDoubleCapMap north (compactCapApproximationRadius (j + 2)) 0
    S := S j
    isSolution := hS j }

def compactCorePointedMaps {D : RealTimeInterval}
    (g : SmoothRiemannianMetric (𝓡 3) E3) (north : S3)
    (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j)) :
    PointedCGHMaps (compactCorePointedFlowSequence north S hS) (compactCorePointedModel g) id where
  partialDiffeomorph j := compactDoubleCorePartialDiffeomorph north (compactCapApproximationRadius (j + 2))
  source_exhausts := core_balls_exhaust
  base_mem := by
    intro j
    change (0 : E3) ∈ Metric.ball 0 (compactCapApproximationRadius (j + 2) - 2)
    rw [Metric.mem_ball, dist_self]
    linarith [compactCapApproximationRadius_large (j + 2), le_max_right transitionEnd 2]
  basepoint_map := fun _ => rfl

section Sequence
variable {D : RealTimeInterval} (g : SmoothRiemannianMetric (𝓡 3) E3) (north : S3)
  (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j))
private local instance (j : ℕ) : TopologicalSpace (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomTop (compactCorePointedMaps g north S hS) j
private local instance (j : ℕ) : ChartedSpace E3 (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomCharted (compactCorePointedMaps g north S hS) j
private local instance (j : ℕ) : T2Space (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomT2 (compactCorePointedMaps g north S hS) j
private local instance (j : ℕ) : IsManifold (𝓡 3) ∞ (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomSmooth (compactCorePointedMaps g north S hS) j

theorem compactCorePointedMaps_sourceSigma : SourceIsSigmaCompact (compactCorePointedMaps g north S hS) :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3)
    (PointedCGHMaps.source_open (compactCorePointedMaps g north S hS) j)

theorem compactCorePointedMaps_targetSigma : TargetIsSigmaCompact (compactCorePointedMaps g north S hS) :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3)
    (PointedCGHMaps.target_open (compactCorePointedMaps g north S hS) j)

private local instance (j : ℕ) : SigmaCompactSpace (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomSigmaOf (compactCorePointedMaps g north S hS) j
    (compactCorePointedMaps_sourceSigma g north S hS j)

theorem compactCorePointedMaps_initial
    (hzero : ∀ j, (S j).base.metric 0 =
      compactDoubleTruncationMetric north (compactCapApproximationRadius (j + 2))
        (compactCapApproximationRadius_large (j + 2)) g) (j : ℕ) :
    sourceMetric (compactCorePointedMaps g north S hS)
      (compactCorePointedMaps_sourceSigma g north S hS)
      (compactCorePointedMaps_targetSigma g north S hS) j 0 =
        sourceMetricRestriction (compactCorePointedMaps g north S hS) g j := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  let Φ := compactCorePointedMaps g north S hS
  let data := SourceDomainMetricData.ofRestrictPullback
    (Φ := Φ) (k := j) (compactCorePointedMaps_sourceSigma g north S hS j)
    (fun _ => g.restrictOpen (sourceOpen Φ j)) (fun _ => g)
  let : TopologicalSpace (SourceDomain Φ j) := data.topology
  let : ChartedSpace E3 (SourceDomain Φ j) := data.charted
  let : T2Space (SourceDomain Φ j) := data.t2
  let : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := data.smooth
  let : SigmaCompactSpace (SourceDomain Φ j) := data.sigmaCompact
  change (data.pullbackMetric 0).inner x v w = g.inner x.val v w
  dsimp only [TangentSpace] at v w ⊢
  erw [data.pullback_inner]
  have hd (u : E3) : mfderiv (𝓡 3) (𝓡 3)
      (fun y : SourceDomain Φ j => Φ.map j y.val) x u =
      mfderiv (𝓡 3) (𝓡 3)
        (compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x.val u := by
    have hh := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3)
      (f := (Subtype.val : SourceDomain Φ j → E3))
      (g := compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x
      ((contMDiff_compactDoubleCapMap north (compactCapApproximationRadius (j + 2))).mdifferentiableAt (by simp))
      (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)) u
    have hinc : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : SourceDomain Φ j → E3) x u = u :=
      mfderiv_subtype_val_apply (I := 𝓡 3) (sourceOpen Φ j) x u
    exact hh.trans (congrArg
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x.val) hinc)
  simp only [hd]
  change ((S j).base.metric 0).inner
    (compactDoubleCapMap north (compactCapApproximationRadius (j + 2)) x.val)
    (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x.val v)
    (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x.val w) = _
  have hslot (p : S3) (u z : TangentSpace (𝓡 3) p) :=
    congrArg (fun m : SmoothRiemannianMetric (𝓡 3) S3 => m.inner p u z) (hzero j)
  exact (hslot _ _ _).trans
    (compactDoubleCorePartialDiffeomorph_truncation_pullback north
      (compactCapApproximationRadius (j + 2)) (compactCapApproximationRadius_large (j + 2))
      g x.val x.property v w)

private local instance (j : ℕ) : TopologicalSpace (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomTop (compactCorePointedMaps g north S hS) j
private local instance (j : ℕ) : ChartedSpace E3 (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomCharted (compactCorePointedMaps g north S hS) j
private local instance (j : ℕ) : T2Space (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomT2 (compactCorePointedMaps g north S hS) j
private local instance (j : ℕ) : IsManifold (𝓡 3) ∞ (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomSmooth (compactCorePointedMaps g north S hS) j
private local instance (j : ℕ) : SigmaCompactSpace (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomSigmaOf (compactCorePointedMaps g north S hS) j
    (compactCorePointedMaps_targetSigma g north S hS j)

private theorem canonical_metric (j : ℕ) (t : ℝ) :
    sourceMetric (compactCorePointedMaps g north S hS)
      (compactCorePointedMaps_sourceSigma g north S hS)
      (compactCorePointedMaps_targetSigma g north S hS) j t =
      Diffeomorph.pullbackMetric
        (((S j).base.metric t).restrictOpen (targetOpen (compactCorePointedMaps g north S hS) j))
        (sourceTargetDiff (compactCorePointedMaps g north S hS) j) := rfl

theorem compactCorePointedMaps_reference_bounds
    (hzero : ∀ j, (S j).base.metric 0 =
      compactDoubleTruncationMetric north (compactCapApproximationRadius (j + 2))
        (compactCapApproximationRadius_large (j + 2)) g)
    (τ Λ : ℝ) (C L : ℕ → ℝ) (hC : ∀ N, 0 ≤ C N) (hL : ∀ N, 0 ≤ L N)
    (he : ∀ j, ∀ t ∈ Icc 0 τ,
      MetricUniformEquivalentOn univ ((S j).base.metric 0) ((S j).base.metric t) Λ)
    (hc : ∀ j N, ∀ t ∈ Icc 0 τ, ∀ x : S3,
      metricCovDerivNorm N ((S j).base.metric t) ((S j).base.metric 0) x ≤ C N)
    (hl : ∀ j N, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ x : S3,
      metricDerivNorm N ((S j).base.metric s) ((S j).base.metric t)
        ((S j).base.metric 0) x ≤ L N * |s - t|) :
    (∀ j, ∀ t ∈ Icc 0 τ,
      MetricUniformEquivalentOn univ (sourceMetricRestriction (compactCorePointedMaps g north S hS) g j)
        (sourceMetric (compactCorePointedMaps g north S hS)
          (compactCorePointedMaps_sourceSigma g north S hS)
          (compactCorePointedMaps_targetSigma g north S hS) j t) Λ) ∧
    SourceMetricCovariantLipschitzBounds (compactCorePointedMaps g north S hS) g
      (compactCorePointedMaps_sourceSigma g north S hS)
      (compactCorePointedMaps_targetSigma g north S hS) 0 τ := by
  let Φ := compactCorePointedMaps g north S hS
  let hsrc := compactCorePointedMaps_sourceSigma g north S hS
  let htgt := compactCorePointedMaps_targetSigma g north S hS
  have hi := compactCorePointedMaps_initial g north S hS hzero
  have hcov (N j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (y : SourceDomain Φ j) :
      metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t) (sourceMetricRestriction Φ g j) y ≤ C N := by
    rw [← hi j, canonical_metric, canonical_metric,
      metricCovDerivNorm_pullback, covNorm_restrictOpen]
    exact hc j N t ht _
  have hlip (N j : ℕ) (s : ℝ) (hs : s ∈ Icc 0 τ)
      (t : ℝ) (ht : t ∈ Icc 0 τ) (y : SourceDomain Φ j) :
      metricDerivNorm N (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
        (sourceMetricRestriction Φ g j) y ≤ L N * |s - t| := by
    rw [← hi j, canonical_metric, canonical_metric, canonical_metric,
      metricDerivNorm_pullback, metricDerivNorm_restrictOpen]
    exact hl j N s hs t ht _
  constructor
  · intro j t ht
    have hr := metricUniformEquivalentOn_restrictOpen univ
      ((S j).base.metric 0) ((S j).base.metric t) Λ (he j t ht)
      (targetOpen Φ j) (V := univ) (fun _ _ => mem_univ _)
    have hp := metricUniformEquivalentOn_pullback univ _ _ Λ hr
      (sourceTargetDiff Φ j) (V := univ) (fun _ _ => mem_univ _)
    rw [← canonical_metric, ← canonical_metric, hi j] at hp
    exact hp
  · constructor
    · intro N
      exact ⟨C N, hC N, fun j t ht y => hcov N j t ht y⟩
    · intro N
      refine ⟨∑ a ∈ Finset.range (N + 1), L a, Finset.sum_nonneg (fun a _ => hL a), ?_⟩
      intro j s t hs ht a ha y
      refine (hlip a j s hs t ht y).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      exact Finset.single_le_sum (s := Finset.range (N + 1)) (a := a) (f := L)
        (fun b _ => hL b) (Finset.mem_range.mpr (by omega))

end Sequence
end DifferentialGeometry.PDE.RicciFlow
