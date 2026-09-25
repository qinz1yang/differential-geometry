import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.RicciTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMixedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RicciFamilyRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedReferenceBounds
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem uniformStandardLifetime_ricci_lipschitz_closed
    (τ : ℝ) (hτ : 0 < τ) (hlt : ENNReal.ofReal τ < uniformStandardLifetime) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ S : StandardSolution,
      ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
        |ricciTensor (S.val.metric s) x v w - ricciTensor (S.val.metric t) x v w| ≤
          L * Real.sqrt ((S.val.metric 0).inner x v v) *
            Real.sqrt ((S.val.metric 0).inner x w w) * |s - t| := by
  obtain ⟨C, hC, hcurv⟩ := uniformStandardLifetime_mixed_bounds_closed τ hτ.le hlt 2
  obtain ⟨Λ, hΛ, hmet⟩ := uniformStandardLifetime_metricComparison τ hτ.le hlt
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  refine ⟨Λ * ricciOrdinaryTimeBound 3 C,
    mul_nonneg hΛ0 (ricciOrdinaryTimeBound_nonneg _ _ hC), ?_⟩
  intro S s hs t ht x v w
  have hslab : Icc 0 τ ⊆ S.val.domain := fun r hr => (hmet S r hr).1
  have hregular : Ioo 0 τ ⊆ (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular := by
    intro r hr
    apply (mem_lifetimeInterval_regular S.val.lifetime S.val.lifetime_pos r).mpr
    exact ⟨hr.1, (ENNReal.ofReal_le_ofReal hr.2.le).trans_lt
      (hlt.trans_le (uniformStandardLifetime_le_lifetime S))⟩
  have hjet : ∀ r ∈ Ioo 0 τ, ∀ k ≤ 2,
      Real.sqrt (nablaKRm04NormSqIntrinsic S.val.toSolutionOn k r x) ≤ C := by
    intro r hr k hk
    exact hcurv S k 0 (by omega) r (Ioo_subset_Icc_self hr) x
  have hm : ∀ r ∈ Ioo 0 τ, ∀ v : TangentSpace (𝓡 3) x,
      (S.val.metric r).inner x v v ≤ Λ * (S.val.metric 0).inner x v v := by
    intro r hr z
    simpa only [S.val.initial] using ((hmet S r (Ioo_subset_Icc_self hr)).2 x z).2
  have hh := S.val.isSolutionOn.ricciTensor_lipschitz_of_curvature_derivative_bound
    (S.val.metric 0) x hΛ0 hC hslab hregular hm hjet hs ht v w
  simpa only [PartialStandardSolution.toSolutionOn_metric, finrank_euclideanSpace_fin] using hh


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

private theorem source_ricci_lipschitz_of_original
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (L : ℝ)
    (hL : ∀ U : StandardSolution,
      ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ (y : E3) (v w : TangentSpace (𝓡 3) y),
        |ricciTensor (U.val.metric s) y v w - ricciTensor (U.val.metric t) y v w| ≤
          L * Real.sqrt ((U.val.metric 0).inner y v v) *
            Real.sqrt ((U.val.metric 0).inner y w w) * |s - t|)
    (j : ℕ) (s : ℝ) (hs : s ∈ Icc 0 τ) (t : ℝ) (ht : t ∈ Icc 0 τ)
    (q : SourceDomain Φ j) (v w : TangentSpace (𝓡 3) q) :
    |ricciTensor (sourceMetric Φ hsrc htgt j s) q v w -
        ricciTensor (sourceMetric Φ hsrc htgt j t) q v w| ≤
      L * Real.sqrt (P.metric.inner q.val v v) *
        Real.sqrt (P.metric.inner q.val w w) * |s - t| := by
  have hzero (z : TangentSpace (𝓡 3) q) :
      ((S (φ j)).val.metric 0).inner (sourceTargetDiff Φ j q).val
        (mfderiv (𝓡 3) (𝓡 3) (sourceTargetDiff Φ j) q z)
        (mfderiv (𝓡 3) (𝓡 3) (sourceTargetDiff Φ j) q z) =
          P.metric.inner q.val z z := by
    have hh := congrArg
      (fun g : SmoothRiemannianMetric (𝓡 3) (SourceDomain Φ j) => g.inner q z z) (hinit j)
    change (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric 0).restrictOpen (targetOpen Φ j))
      (sourceTargetDiff Φ j)).inner q z z =
        (P.metric.restrictOpen (sourceOpen Φ j)).inner q z z at hh
    simpa only [Diffeomorph.pullbackMetric_inner,
      SmoothRiemannianMetric.restrictOpen_inner] using hh
  have hh := hL (S (φ j)) s hs t ht (sourceTargetDiff Φ j q).val
    (mfderiv (𝓡 3) (𝓡 3) (sourceTargetDiff Φ j) q v)
    (mfderiv (𝓡 3) (𝓡 3) (sourceTargetDiff Φ j) q w)
  rw [hzero v, hzero w] at hh
  change |ricciTensor (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric s).restrictOpen (targetOpen Φ j)) (sourceTargetDiff Φ j)) q v w -
    ricciTensor (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric t).restrictOpen (targetOpen Φ j)) (sourceTargetDiff Φ j)) q v w| ≤ _
  simpa only [CheegerGromovCompactness.ricciTensor_pullback,
    DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen, mfderiv_subtype_val_apply] using hh

end Maps

theorem standard_closed_source_ricci_lipschitz
    (τ : ℝ) (hτ : 0 < τ) (hlt : ENNReal.ofReal τ < uniformStandardLifetime) :
    ∃ L : ℝ, 0 ≤ L ∧
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
        ∀ j : ℕ,
          letI : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
          letI : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j
          letI : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
          letI : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
          letI : SigmaCompactSpace (SourceDomain Φ j) := sourceDomSigmaOf Φ j (hsrc j)
          ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ,
            ∀ (q : SourceDomain Φ j) (v w : TangentSpace (𝓡 3) q),
              |ricciTensor (sourceMetric Φ hsrc htgt j s) q v w -
                  ricciTensor (sourceMetric Φ hsrc htgt j t) q v w| ≤
                L * Real.sqrt (P.metric.inner q.val v v) *
                  Real.sqrt (P.metric.inner q.val w w) * |s - t| := by
  obtain ⟨L, hL, hactual⟩ := uniformStandardLifetime_ricci_lipschitz_closed τ hτ hlt
  refine ⟨L, hL, ?_⟩
  intro S x P φ Φ hsrc htgt hinit
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace E3 P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold (𝓡 3) ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  intro j
  let : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
  let : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j
  let : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
  let : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
  let : SigmaCompactSpace (SourceDomain Φ j) := sourceDomSigmaOf Φ j (hsrc j)
  exact source_ricci_lipschitz_of_original Φ hsrc htgt hinit L hactual j

end DifferentialGeometry.PDE.RicciFlow

end
