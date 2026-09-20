import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactness

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_backward_flow_compactness_with_uniform_metric_convergence
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) :
    let X := backwardFlowSequence F tau htau q
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧ ∃ Phi : PointedCGHMaps (I := I) X (L.atTime 0) phi,
        ConnectedSpace L.M ∧ (∀ t : ℝ, t ≤ 0 → MetricComplete (L.atTime t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∃ C : MetricConvergenceData (I := I) (Phi.atTime (I := I) (X := X) (L := L) t),
          (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I)
            (Phi.atTime (I := I) (X := X) (L := L) t) k) ∧
          (∀ k,
            let D := C.domain k
            let _ : TopologicalSpace (MetricSourceDomain (I := I) (Phi.atTime (I := I) (X := X) (L := L) t) k) := D.topology
            let _ : ChartedSpace H (MetricSourceDomain (I := I) (Phi.atTime (I := I) (X := X) (L := L) t) k) := D.charted
            let _ : IsManifold I ∞ (MetricSourceDomain (I := I) (Phi.atTime (I := I) (X := X) (L := L) t) k) := D.smooth
            D.referenceMetric = D.limitMetric)) ∧
        ∃ (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M),
          (∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
            ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
              ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
                (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner
                  (Phi.map i x) (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)) ∧
          (∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
            ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ i ≥ N,
              ∀ t ∈ Icc a b,
                metricDerivNormSupOn K p (G i t) (L.S.base.metric t) R < epsilon) := by
  let X := backwardFlowSequence F tau htau q
  have htime (i : ℕ) (t : ℝ) (ht : t ≤ 0) : tau i * (t - 1) ≤ -tau i := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (htau i).le ht]
  have hcomplete : FlowMetricComplete X := by
    constructor
    intro i t ht
    have hc : RiemannianMetricComplete (F.S.base.metric (tau i * (t - 1))) :=
      ⟨hF.complete _ ((htime i t ht).trans (neg_nonpos.mpr (htau i).le))⟩
    have hscaled : RiemannianMetricComplete ((X.term i).S.base.metric t) := by
      rw [backwardFlowSequence_metric]
      exact hc.of_lower (inv_pos.mpr (htau i)) (fun _ _ => le_rfl)
    exact hscaled.complete
  have hconnected (i : ℕ) : ConnectedSpace (X.term i).M := hF.connected
  obtain ⟨eta, heta, hbound⟩ := exists_backwardSliceSequence_injRadius_bound
    F hF p tau htau q hbase (D := 0) le_rfl
  have hinj : FlowScaleInjectivityBound X := by
    change BaseInjBound (backwardFlowSequence F tau htau q).atZero
    rw [backwardFlowSequence_atZero]
    exact ⟨eta, heta, fun i => hbound i (q i) (by simp only [riemannianEDistOf_self]; positivity)⟩
  have hlocal : ∀ R : ℝ, 0 < R → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (X.term i).M,
        riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤
          ENNReal.ofReal R → (X.term i).rmNormSq t x ≤ K := by
    intro R hR T _hT
    let K := (Module.finrank ℝ E : ℝ) ^ 2 *
      (3 * (Real.sqrt A + Real.sqrt 3 / 2 * R) ^ 2)
    refine ⟨K ^ 2, sq_nonneg K, Filter.Eventually.of_forall ?_⟩
    intro i t ht x hx
    have hd : riemannianEDistOf
        (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i)))
        (q i) x ≤ ENNReal.ofReal R := by
      convert hx using 1
      simp only [X, backwardFlowSequence, curvatureNormalizedFlow, curvatureNormalizedSolution,
        SolutionOn.timeRestrict, parabolicSolution, parabolicFamily, parabolicTime_zero]
      rfl
    have h := rmNorm_le_on_past_of_rescaled_distance_le F hF p (q i) x (htau i)
      hR.le (hbase i) hd (htime i t ht.2)
    change Tensor0SBundle.normSq0S ((X.term i).S.base.metric t) x 4
      (metricRm04At ((X.term i).S.base.metric t) x) ≤ K ^ 2
    rw [backwardFlowSequence_metric]
    exact (Real.sqrt_le_iff.mp h).2
  have hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
        c * ((X.term i).S.base.metric 0).inner x v v ≤
          ((X.term i).S.base.metric t).inner x v v := by
    intro T _hT
    refine ⟨1, one_pos, Filter.Eventually.of_forall ?_⟩
    intro i t ht x v
    rw [one_mul, backwardFlowSequence_metric, backwardFlowSequence_metric]
    simp only [zero_sub, mul_neg_one]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (htau i)).le
    exact ancientModel_metric_inner_antitoneOn F hF x v
      ((htime i t ht.2).trans (neg_nonpos.mpr (htau i).le))
      (neg_nonpos.mpr (htau i).le) (htime i t ht.2)
  have hcarrier : X.D.carrier = Iic 0 := rfl
  obtain ⟨L, phi, hphi, Phi, hconn, hcomp, hconv, hmetric⟩ :=
    exists_local_ancient_flow_compactness_with_uniform_metric_convergence X rfl hcomplete hconnected hinj hlocal hlower
  refine ⟨L, phi, hphi, Phi, hconn, ?_, ?_, hmetric⟩
  · intro t ht
    exact hcomp t ht
  · simpa only [hcarrier, Set.mem_Iic] using hconv

theorem exists_backward_flow_compactness
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) :
    let X := backwardFlowSequence F tau htau q
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧ ∃ Phi : PointedCGHMaps (I := I) X (L.atTime 0) phi,
        ConnectedSpace L.M ∧ (∀ t : ℝ, t ≤ 0 → MetricComplete (L.atTime t)) ∧
        ∀ t : ℝ, t ≤ 0 → ∃ C : MetricConvergenceData (I := I) (Phi.atTime (I := I) (X := X) (L := L) t),
          (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I)
            (Phi.atTime (I := I) (X := X) (L := L) t) k) ∧
          (∀ k,
            let D := C.domain k
            let _ : TopologicalSpace (MetricSourceDomain (I := I) (Phi.atTime (I := I) (X := X) (L := L) t) k) := D.topology
            let _ : ChartedSpace H (MetricSourceDomain (I := I) (Phi.atTime (I := I) (X := X) (L := L) t) k) := D.charted
            let _ : IsManifold I ∞ (MetricSourceDomain (I := I) (Phi.atTime (I := I) (X := X) (L := L) t) k) := D.smooth
            D.referenceMetric = D.limitMetric) := by
  obtain ⟨L, phi, hphi, Phi, hconn, hcomp, hconv, _⟩ :=
    exists_backward_flow_compactness_with_uniform_metric_convergence F hF p tau htau q hbase
  exact ⟨L, phi, hphi, Phi, hconn, hcomp, hconv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2

theorem backward_flow_limit_metric_inner_antitoneOn
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {J : Set ℝ} (hJ : J ⊆ Iic 0)
    (hmetric : ∀ t : ℝ, t ∈ J → ∀ x : L.M, ∀ v : TangentSpace I x,
      Tendsto (fun n => (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
        (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x v))
        atTop (𝓝 ((L.S.base.metric t).inner x v v)))
    (x : L.M) (v : TangentSpace I x) :
    AntitoneOn (fun t => (L.S.base.metric t).inner x v v) J := by
  intro s hs t ht hst
  apply le_of_tendsto_of_tendsto (hmetric t ht x v) (hmetric s hs x v)
  filter_upwards [] with n
  rw [backwardFlowSequence_metric, backwardFlowSequence_metric]
  change (tau (subseq n))⁻¹ * (F.S.base.metric (tau (subseq n) * (t - 1))).inner
    (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x v) ≤
    (tau (subseq n))⁻¹ * (F.S.base.metric (tau (subseq n) * (s - 1))).inner
      (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x v)
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (htau (subseq n)).le)
  apply ancientModel_metric_inner_antitoneOn F hF
  · exact mul_nonpos_of_nonneg_of_nonpos (htau (subseq n)).le (sub_nonpos.mpr (le_trans (hJ hs) zero_le_one))
  · exact mul_nonpos_of_nonneg_of_nonpos (htau (subseq n)).le (sub_nonpos.mpr (le_trans (hJ ht) zero_le_one))
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_right hst 1) (htau (subseq n)).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
