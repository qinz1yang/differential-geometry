import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.DistanceControl
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.CovariantDerivative
import DifferentialGeometry.Topology.SigmaCompactOpen

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Set Topology TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N]
variable {P : Type u} [TopologicalSpace P] [ChartedSpace H P]
  [IsManifold I ∞ P] [T2Space P]

theorem pullback_metric_cov_deriv_norm_eq
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {K : Set M} (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hUK : (U : Set M) ⊆ K)
    (gRef : SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I N)
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) gRef g)
    (q : ℕ) (x : U) :
    metricCovDerivNorm (I := I) q (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
        (gRef.restrictOpen (I := I) U) x =
      tensor02CovDerivNormWith (I := I) q D.pullback gRef gRef (x : M) := by
  let hB := PartialDiffeomorph.pullbackMetricOn Φ U hU g
  have hbase : ∀ (y : U) (slots : Fin 2 → TangentSpace I y),
      Tensor0SBundle.metricTensorField (I := I) hB y slots =
        D.pullback (y : M) slots := by
    intro y slots
    rw [Tensor0SBundle.metricTensorField_apply, PartialDiffeomorph.pullbackMetricOn_inner]
    exact (D.pullback_apply (y : M) (hUK y.2) slots).symm
  have htower := covDerivOfField_restrictOpen (I := I) gRef U
    (Tensor0SBundle.metricTensorField (I := I) hB) D.pullback hbase q x
  have hT : metricCovDeriv (I := I) hB (gRef.restrictOpen (I := I) U) q x =
      covDerivOfField (I := I) gRef D.pullback q (x : M) := by
    rw [metricCovDeriv_eq_covDerivOfField]
    exact ContinuousMultilinearMap.ext htower
  unfold metricCovDerivNorm tensor02CovDerivNormWith
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, hT]
  congr 1
  exact normSq0S_restrictOpen_apply (I := I) gRef U (q + 2) x _

theorem pullback_metric_cov_deriv_norm_le
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {K : Set M} (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hUK : (U : Set M) ⊆ K)
    (gRef : SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I N)
    {ε : ℝ} {p q : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) gRef g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    metricCovDerivNorm (I := I) q (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
      (gRef.restrictOpen (I := I) U) x ≤ ε := by
  rw [pullback_metric_cov_deriv_norm_eq Φ U hU hUK gRef g D q x]
  exact D.cov_deriv_small q hq1 hqp (x : M) (hUK x.2)

theorem trans_pullback_metric_cov_deriv_norm_le
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞))
    {K : Set N} (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hnext : (Φ : M → N) '' (U : Set M) ⊆ Θ.source)
    (hUK : (Φ : M → N) '' (U : Set M) ⊆ K)
    (gMid : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I P)
    {ε : ℝ} {p q : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Θ : N → P) gMid g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) q
        (PartialDiffeomorph.pullbackMetricOn
          (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U
          (PartialDiffeomorph.subset_trans_source Φ Θ U hU hnext) g)
        (PartialDiffeomorph.pullbackMetricOn Φ U hU gMid) x ≤ ε := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  rw [PartialDiffeomorph.pullbackMetricOn_trans]
  · let W : Opens N :=
      ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
    let _ : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
    let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
      PartialDiffeomorph.toOpensDiffeo Φ hU
    change metricCovDerivNorm (I := I) q
        (Diffeomorph.pullbackMetric (I := I)
          (PartialDiffeomorph.pullbackMetricOn Θ W hnext g) F)
        (Diffeomorph.pullbackMetric (I := I) (gMid.restrictOpen (I := I) W) F) x ≤ ε
    rw [metricCovDerivNorm_pullback (I := I)]
    exact pullback_metric_cov_deriv_norm_le Θ W hnext hUK gMid g D hq1 hqp (F x)

theorem pullback_metric_inner_lower
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {K : Set M} (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hUK : (U : Set M) ⊆ K)
    (gRef : SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I N)
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) gRef g)
    (x : U) (v : TangentSpace I x) :
    (1 - ε) * (gRef.restrictOpen (I := I) U).inner x v v ≤
      (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v := by
  let vM : TangentSpace I (x : M) := (v : E)
  calc
    (1 - ε) * (gRef.restrictOpen (I := I) U).inner x v v =
        (1 - ε) * gRef.inner (x : M) vM vM := rfl
    _ ≤ D.pullback (x : M) (fun _ => vM) :=
      (tensor_apply_bounds_of_metricTensorErrorNorm_le
        D.pullback gRef (D.c0_small (x : M) (hUK x.2)) vM).1
    _ = (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v := by
      with_unfolding_all
        rw [D.pullback_apply (x : M) (hUK x.2),
          PartialDiffeomorph.pullbackMetricOn_inner]

theorem pullback_metric_inner_upper
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {K : Set M} (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hUK : (U : Set M) ⊆ K)
    (gRef : SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I N)
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) gRef g)
    (x : U) (v : TangentSpace I x) :
    (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v ≤
      (1 + ε) * (gRef.restrictOpen (I := I) U).inner x v v := by
  let vM : TangentSpace I (x : M) := (v : E)
  calc
    (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v =
        D.pullback (x : M) (fun _ => vM) := by
      with_unfolding_all
        rw [D.pullback_apply (x : M) (hUK x.2),
          PartialDiffeomorph.pullbackMetricOn_inner]
    _ ≤ (1 + ε) * gRef.inner (x : M) vM vM :=
      (tensor_apply_bounds_of_metricTensorErrorNorm_le (I := I)
        D.pullback gRef (D.c0_small (x : M) (hUK x.2)) vM).2
    _ = (1 + ε) * (gRef.restrictOpen (I := I) U).inner x v v := rfl

theorem pullback_metric_zero_cov_deriv_norm_le
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {K : Set M} (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hUK : (U : Set M) ⊆ K)
    (gRef : SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I N)
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) gRef g)
    (hε : ε ≤ 1 / 2) (x : U) :
    metricCovDerivNorm (I := I) 0 (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
        (gRef.restrictOpen (I := I) U) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  apply covNorm0_le (I := I) (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
    (gRef.restrictOpen (I := I) U) x (C := 2) (by norm_num)
  intro v
  have hl := pullback_metric_inner_lower Φ U hU hUK gRef g D x v
  have hu := pullback_metric_inner_upper Φ U hU hUK gRef g D x v
  have hnn : 0 ≤ (gRef.restrictOpen (I := I) U).inner x v v :=
    metric_inner_self_nonneg (I := I) (gRef.restrictOpen (I := I) U) x v
  constructor
  · have hu' : (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v ≤
        (3 / 2 : ℝ) * (gRef.restrictOpen (I := I) U).inner x v v := by
      nlinarith
    calc
      (2 : ℝ)⁻¹ * (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v =
          (1 / 2 : ℝ) * (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v v := by
            norm_num
      _ ≤ (1 / 2 : ℝ) * ((3 / 2 : ℝ) *
          (gRef.restrictOpen (I := I) U).inner x v v) :=
        mul_le_mul_of_nonneg_left hu' (by norm_num)
      _ ≤ (gRef.restrictOpen (I := I) U).inner x v v := by nlinarith
  · nlinarith

theorem trans_pullback_metric_zero_cov_deriv_norm_le
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞))
    {K : Set N} (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hnext : (Φ : M → N) '' (U : Set M) ⊆ Θ.source)
    (hUK : (Φ : M → N) '' (U : Set M) ⊆ K)
    (gMid : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I P)
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Θ : N → P) gMid g)
    (hε : ε ≤ 1 / 2) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) 0
        (PartialDiffeomorph.pullbackMetricOn
          (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U
          (PartialDiffeomorph.subset_trans_source Φ Θ U hU hnext) g)
        (PartialDiffeomorph.pullbackMetricOn Φ U hU gMid) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  rw [PartialDiffeomorph.pullbackMetricOn_trans]
  · let W : Opens N :=
      ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
    let _ : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
    let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
      PartialDiffeomorph.toOpensDiffeo Φ hU
    change metricCovDerivNorm (I := I) 0
        (Diffeomorph.pullbackMetric (I := I)
          (PartialDiffeomorph.pullbackMetricOn Θ W hnext g) F)
        (Diffeomorph.pullbackMetric (I := I) (gMid.restrictOpen (I := I) W) F) x ≤ _
    rw [metricCovDerivNorm_pullback (I := I)]
    exact pullback_metric_zero_cov_deriv_norm_le Θ W hnext hUK gMid g D hε (F x)

theorem pullback_metric_deriv_norm_le
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {K : Set M} (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hUK : (U : Set M) ⊆ K)
    (gRef : SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I N)
    {ε : ℝ} {p q : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) gRef g)
    (hqp : q ≤ p) (x : U) :
    metricDerivNorm (I := I) q (PartialDiffeomorph.pullbackMetricOn Φ U hU g)
      (gRef.restrictOpen (I := I) U) (gRef.restrictOpen (I := I) U) x ≤ ε := by
  let hB := PartialDiffeomorph.pullbackMetricOn Φ U hU g
  let gU := gRef.restrictOpen (I := I) U
  by_cases hq0 : q = 0
  · subst q
    have hpb : Tensor0SBundle.metricTensorField (I := I) hB x = D.pullback (x : M) := by
      apply ContinuousMultilinearMap.ext
      intro slots
      let slotsM : Fin 2 → TangentSpace I (x : M) := fun i => (slots i : E)
      change hB.inner x (slots 0) (slots 1) = D.pullback (x : M) slotsM
      with_unfolding_all
        rw [PartialDiffeomorph.pullbackMetricOn_inner]
      exact (D.pullback_apply (x : M) (hUK x.2) slotsM).symm
    have href : Tensor0SBundle.metricTensorField (I := I) gU x =
        Tensor0SBundle.metricTensorField (I := I) gRef (x : M) := by
      apply ContinuousMultilinearMap.ext
      intro slots
      change gU.inner x (slots 0) (slots 1) =
        gRef.inner (x : M) (slots 0) (slots 1)
      rfl
    unfold metricDerivNorm metricDiffCovDerivAt
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gU x 2
      (Tensor0SBundle.metricTensorField (I := I) hB x -
        Tensor0SBundle.metricTensorField (I := I) gU x)) ≤ ε
    rw [hpb, href, normSq0S_restrictOpen_apply (I := I)]
    exact D.c0_small (x : M) (hUK x.2)
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hzero : metricCovDeriv (I := I) gU gU q x = 0 := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      rw [metricCovDeriv_eq_covDerivOfField, covDerivOfField_eq_iterCov,
        iterCov_metric_zero]
      exact DFunLike.congr_fun (MultilinearSection.domDomCongr_zero
        (IB := I) (F := E) (n := (∞ : WithTop ℕ∞)) (acEquiv r.succ)) x
    unfold metricDerivNorm metricDiffCovDerivAt
    rw [hzero, sub_zero]
    exact pullback_metric_cov_deriv_norm_le Φ U hU hUK gRef g D hq1 hqp x

end HCGCompactness
end DifferentialGeometry
