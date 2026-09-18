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
  obtain ⟨L, phi, hphi, Phi, hconn, hcomp, hconv⟩ :=
    exists_local_ancient_flow_compactness X rfl hcomplete hconnected hinj hlocal hlower
  refine ⟨L, phi, hphi, Phi, hconn, ?_, ?_⟩
  · intro t ht
    exact hcomp t ht
  · simpa only [hcarrier, Set.mem_Iic] using hconv

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
